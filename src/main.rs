#![feature(rustc_private)]
#![allow(unused_imports)]
#![feature(lazy_cell)]
#![feature(lazy_cell_consume)]

// sources
// https://github.com/rust-lang/miri/blob/master/benches/helpers/miri_helper.rs
// https://github.com/rust-lang/rust/blob/master/src/test/run-make-fulldeps/obtain-borrowck/driver.rs
// https://github.com/viperproject/prusti-dev/blob/master/analysis/src/bin/analysis-driver.rs

extern crate rustc_ast_pretty;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_error_codes;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

use rustc_ast_pretty::pprust::item_to_string;
use rustc_data_structures::steal::Steal;
use rustc_driver::Compilation;
use rustc_errors::registry;
use rustc_middle::middle::provide;
use rustc_middle::mir::Location;
use rustc_middle::mir::SourceInfo;
use rustc_middle::mir::SourceScope;
use rustc_middle::mir::{
    BasicBlock, BasicBlockData, Body, Statement, StatementKind, Terminator, TerminatorKind,
    OUTERMOST_SOURCE_SCOPE,
};
use rustc_middle::query::queries::mir_built::{self, ProvidedValue};
use rustc_middle::query::Providers;
use rustc_middle::ty;
use rustc_session::config::{self, CheckCfg};
use rustc_session::EarlyErrorHandler;
use rustc_span::def_id::LocalDefId;
use rustc_span::source_map;
use rustc_span::DUMMY_SP;
use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::mem;
use std::sync::LazyLock;
use std::thread::current;
use std::{path, process, str};

#[allow(dead_code)]
struct OurCompilerCalls {
    args: Vec<String>,
}

const FORGED_SOURCE_INFO: SourceInfo = SourceInfo {
    span: DUMMY_SP,
    scope: OUTERMOST_SOURCE_SCOPE,
};

struct BodyModifier<'mir, 'tcx> {
    /// MIR body under modification
    body: &'mir mut Body<'tcx>,

    /// Mapping from original locations to locations in the current MIR
    location_table: BTreeMap<Location, Location>,
}

#[allow(unused)]
impl<'mir, 'tcx: 'mir> BodyModifier<'mir, 'tcx> {
    pub fn new<'a>(body: &'a mut Body<'tcx>) -> Self
    where
        'a: 'mir,
    {
        // Initial location table is the identity
        let mut location_table: BTreeMap<Location, Location> = Default::default();
        for (block, bb_data) in body.basic_blocks.iter_enumerated() {
            for statement_index in 0..=(bb_data.statements.len()) {
                location_table.insert(
                    Location {
                        block,
                        statement_index,
                    },
                    Location {
                        block,
                        statement_index,
                    },
                );
            }
        }
        Self {
            body,
            location_table,
        }
    }

    /// Example: turns a statement into a nop
    /// location must not be a terminator (in the original MIR)
    pub fn make_nop_at(&mut self, loc: &Location) {
        let current_loc = self.location_table.get(loc).unwrap();
        self.body.basic_blocks_mut()[current_loc.block].statements[current_loc.statement_index]
            .make_nop();
    }

    /// Example: Overwrites all (original) locations as nop
    /// locations corresponding to newly issued statements will not be overwritten
    pub fn overwrite_all_as_nop(&mut self) {
        for block_ix in 0..(self.body.basic_blocks.len()) {
            for statement_index in 0..(self.body.basic_blocks[block_ix.into()].statements.len()) {
                let loc = Location {
                    block: block_ix.into(),
                    statement_index,
                }
                .clone();
                self.make_nop_at(&loc);
            }
        }
    }

    /// Insert nop
    /// Shift every statment in the current block down by one
    /// if location is the terminator, this function inserts it at the end of the statements list
    // pub fn insert_nop_before(&mut self, loc: &Location) {
    //     let current_loc = self.location_table.get(loc).unwrap();
    //     let current_block_statements =
    //         &mut (self.body.basic_blocks.as_mut_preserves_cfg()[current_loc.block]).statements;
    //     // Allocate space for the nop
    //     current_block_statements.push(Statement {
    //         source_info: FORGED_SOURCE_INFO.clone(),
    //         kind: StatementKind::Nop,
    //     });
    //     todo!()
    // }

    fn allocate_block(&mut self) -> BasicBlock {
        let block = self.body.basic_blocks.len().into();
        let default_block_data = BasicBlockData {
            statements: vec![],
            terminator: None,
            is_cleanup: false,
        };
        assert_eq!(
            block,
            self.body.basic_blocks.as_mut().push(default_block_data)
        );
        return block;
    }

    fn set_terminator(&mut self, block: BasicBlock, terminator: Option<Terminator<'tcx>>) {
        self.body.basic_blocks.as_mut()[block].terminator = terminator;
    }

    fn set_statements(&mut self, block: BasicBlock, statements: Vec<Statement<'tcx>>) {
        self.body.basic_blocks.as_mut()[block].statements = statements;
    }

    fn get_data_mut(&mut self, block: BasicBlock) -> &mut BasicBlockData<'tcx> {
        self.body
            .basic_blocks
            .as_mut()
            .as_mut_slice()
            .get_mut(block)
            .unwrap()
    }

    // Splits a block before the given location
    pub fn allocate_test_branch_before(&mut self, loc: &Location) -> BasicBlock {
        // Generate fresh block indices for the test block and continuation block
        let kont_block: BasicBlock = self.allocate_block();
        let test_block: BasicBlock = self.allocate_block();

        // current location corresponding to loc
        let current_loc = *self.location_table.get(loc).unwrap();
        let current_block = current_loc.block;
        let current_block_data = self.get_data_mut(current_block);

        // Copy out the data for the continuation
        let kont_statements = current_block_data.statements[current_loc.statement_index..].to_vec();
        let kont_terminator = current_block_data.terminator.clone();

        // Keep only the statements before the split in the old block
        current_block_data.statements =
            current_block_data.statements[0..current_loc.statement_index].to_vec();

        // collect the MIR statements that belong in the continuation
        self.set_terminator(kont_block, kont_terminator);
        self.set_statements(kont_block, kont_statements);

        // Update the terminator of the old block to be a FalseEdge
        let new_current_terminator = Some(Terminator {
            source_info: FORGED_SOURCE_INFO.clone(),
            kind: TerminatorKind::FalseEdge {
                real_target: kont_block,
                imaginary_target: test_block,
            },
        });
        self.set_terminator(current_block, new_current_terminator);

        // Set up the test block
        let test_terminator = Some(Terminator {
            source_info: FORGED_SOURCE_INFO.clone(),
            kind: TerminatorKind::Unreachable,
        });
        self.set_terminator(test_block, test_terminator);

        // Update the current indicies of all locations which got moved.
        // Moved locations have their value block equal to current block
        //  and their statement index equal or after current_loc
        //  1. point to the freshly generated block
        //  2. subtract current_loc.statement_index from their statement_index
        // looking up loc should return (Location { kont_block, 0 }).
        for (k_loc, v_loc) in self.location_table.iter_mut() {
            if (v_loc.block == current_loc.block)
                && (v_loc.statement_index >= current_loc.statement_index)
            {
                *v_loc = Location {
                    block: kont_block,
                    statement_index: v_loc.statement_index - current_loc.statement_index,
                }
            }
        }

        // Return the index of the test block, to be populated by another function
        return test_block;
    }
}

#[allow(clippy::needless_lifetimes)]
fn mir_built<'tcx>(tcx: ty::TyCtxt<'tcx>, def_id: LocalDefId) -> ProvidedValue<'tcx> {
    // execute the default provider and obtain the MIR
    let mut providers = Providers::default();
    rustc_middle::middle::provide(&mut providers);
    let mir_built_ptr = rustc_interface::DEFAULT_QUERY_PROVIDERS.mir_built;
    let mut body = mir_built_ptr(tcx, def_id).steal();
    println!("=================================");
    println!("[log] initial MIR: {:#?}", body.basic_blocks);

    // Modify and return the MIR
    let mut body_modifier = BodyModifier::new(&mut body);
    let tb0 = body_modifier.allocate_test_branch_before(&Location {
        block: BasicBlock::from_u32(0),
        statement_index: 5,
    });
    println!("first test block is {:?}", tb0);

    // let tb1 = body_modifier.allocate_test_branch_before(&Location {
    //     block: BasicBlock::from_u32(0),
    //     statement_index: 5,
    // });
    // println!("second test block is {:?}", tb1);
    // println!("=================================");
    // println!("[log] modified MIR: {:#?}", body.basic_blocks);
    return tcx.alloc_steal_mir(body);
}

fn override_queries(
    _session: &rustc_session::Session,
    local: &mut rustc_middle::query::Providers,
    _external: &mut rustc_middle::query::ExternProviders,
) {
    // https://doc.rust-lang.org/stable/nightly-rustc/rustc_middle/query/struct.Providers.html
    // todo!("implement the override");
    // local.mir_borrowck = mir_borrowck;
    local.mir_built = mir_built;
}

impl rustc_driver::Callbacks for OurCompilerCalls {
    fn config(&mut self, config: &mut rustc_interface::Config) {
        assert!(config.override_queries.is_none());
        config.override_queries = Some(override_queries);
    }

    fn after_analysis<'tcx>(
        &mut self,
        _error_handler: &rustc_session::EarlyErrorHandler,
        compiler: &rustc_interface::interface::Compiler,
        _queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> Compilation {
        println!("=================================");
        println!("[info] analysis phase complete");

        compiler.enter(|queries| {
            queries.global_ctxt().unwrap().enter(|tcx| {
                println!("[info] entered the compiler");

                let (main_id, main_entry_ty) = tcx.entry_fn(()).unwrap();
                println!("[info] entry fn def_id: {:?}", main_id);
                println!("[info] entry fn ty: {:?}", main_entry_ty);

                assert!(tcx.is_mir_available(main_id), "MIR is unavailable");

                let mir = tcx.mir_built(main_id.as_local().unwrap());

                println!("=================================");
                println!(
                    "[info] final MIR basic blocks: {:#?}",
                    mir.borrow().basic_blocks
                );
            });
        });

        Compilation::Stop
    }
}

fn main() {
    let mut compiler_args = Vec::new();
    let mut callback_args = Vec::new();
    for arg in std::env::args() {
        if arg.starts_with("--analysis") {
            callback_args.push(arg);
        } else {
            compiler_args.push(arg);
        }
    }
    compiler_args.push("-Zpolonius".to_owned());
    compiler_args.push("-Zalways-encode-mir".to_owned());
    compiler_args.push("-Zcrate-attr=feature(register_tool)".to_owned());
    compiler_args.push("-Zcrate-attr=register_tool(analyzer)".to_owned());
    let mut callbacks = OurCompilerCalls {
        args: callback_args,
    };

    rustc_driver::RunCompiler::new(&compiler_args, &mut callbacks)
        .run()
        .expect("compiler returned an err");
}
