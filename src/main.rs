#![feature(rustc_private)]
#![allow(unused_imports)]

extern crate rustc_ast_pretty;
extern crate rustc_driver;
extern crate rustc_error_codes;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_session;
extern crate rustc_span;

use rustc_ast_pretty::pprust::item_to_string;
use rustc_errors::registry;
use rustc_session::config::{self, CheckCfg};
use rustc_span::source_map;
use std::env;
use std::fs;
use std::{path, process, str};

fn main() {
    // get the Rust source
    let args: Vec<String> = env::args().collect();
    assert!(
        args.len() == 2,
        "expected one rust source file, got {:?}",
        args.len()
    );
    let path = &args[1];
    let source = fs::read_to_string(path).expect(&format!("error reading {:?}", path));
    // println!("[source]\n{:?}\n", source);

    // setup the compiler
    let out = process::Command::new("rustc")
        .arg("--print=sysroot")
        .current_dir(".")
        .output()
        .unwrap();
    let sysroot = str::from_utf8(&out.stdout).unwrap().trim();

    // let locale_resources: &'static [&'static str] = &[rustc_interface::DEFAULT_LOCALE_RESOURCE];
    let config = rustc_interface::Config {
        opts: config::Options {
            maybe_sysroot: Some(path::PathBuf::from(sysroot)),
            unstable_opts: config::UnstableOptions {
                polonius: true,
                always_encode_mir: true,
                dump_mir: Some("all".into()),
                ..config::UnstableOptions::default()
            },
            ..config::Options::default()
        },
        input: config::Input::Str {
            name: source_map::FileName::Custom("main.rs".to_string()),
            input: source.to_string(),
        },
        crate_cfg: rustc_hash::FxHashSet::default(),
        crate_check_cfg: CheckCfg::default(),
        output_dir: None,
        output_file: None,
        file_loader: None,
        ice_file: None,
        locale_resources: rustc_driver::DEFAULT_LOCALE_RESOURCES,
        lint_caps: rustc_hash::FxHashMap::default(),
        parse_sess_created: None,
        register_lints: None,
        override_queries: None,
        make_codegen_backend: None,
        registry: registry::Registry::new(&rustc_error_codes::DIAGNOSTICS),
    };

    rustc_interface::run_compiler(config, |compiler| {
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
    });
}
