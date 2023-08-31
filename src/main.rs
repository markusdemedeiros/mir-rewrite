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
use rustc_driver::Compilation;
use rustc_errors::registry;
use rustc_middle::middle::provide;
use rustc_middle::mir::Location;
use rustc_middle::mir::{BasicBlock, BasicBlockData, Body, StatementKind};
use rustc_middle::query::queries::mir_built::{self, ProvidedValue};
use rustc_middle::query::Providers;
use rustc_middle::ty;
use rustc_session::config::{self, CheckCfg};
use rustc_session::EarlyErrorHandler;
use rustc_span::def_id::LocalDefId;
use rustc_span::source_map;
use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::sync::LazyLock;
use std::{path, process, str};

use rustc_data_structures::steal::Steal;

#[allow(dead_code)]
struct OurCompilerCalls {
    args: Vec<String>,
}

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
    body_modifier.overwrite_all_as_nop();

    println!("=================================");
    println!("[log] modified MIR: {:#?}", body.basic_blocks);
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
                println!("[info] MIR basic blocks: {:#?}", mir.borrow().basic_blocks);
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
