use circ::ir::term::*;
use fxhash::FxHashMap;
use itertools::Itertools;
use circ::cfg::clap::{self, Parser};

use std::fs::read_to_string;
use std::iter::FromIterator;

#[derive(Debug, Parser)]
#[command(name = "smt", about = "Exhaustion SMT solver")]
struct Options {
    #[arg()]
    /// Path to serialized IR file
    path: String,
}

fn main() -> Result<(), String> {
    env_logger::Builder::from_default_env()
        .format_level(false)
        .format_timestamp(None)
        .init();
    let opts = Options::parse();
    let contents = read_to_string(&opts.path).unwrap();
    let term = text::parse_term(contents.as_bytes());
    let vars = extras::free_variables_with_sorts(term.clone());
    let vars: Vec<_> = vars.into_iter().collect();
    for (_v, s) in &vars {
        match s {
            Sort::BitVector(..) | Sort::Bool => {}
            _ => {
                println!("unknown");
                return Ok(());
            }
        }
    }
    let sort = check(&term);
    if sort != Sort::Bool {
        return Err(format!("Term has sort {}, not boolean", sort));
    }
    let values: Vec<Vec<Value>> = vars
        .iter()
        .map(|(_, s)| s.elems_iter_values().collect())
        .collect();
    let lin_term = lin::LinTerm::from(&term);
    let mut ivalues = vec![Value::Bool(true); lin_term.steps.len()];
    for vals in values.into_iter().multi_cartesian_product() {
        let env: FxHashMap<String, Value> = vars
            .iter()
            .zip(vals)
            .map(|((var, _), val)| (var.clone(), val))
            .collect();
        for i in 0..ivalues.len() {
            let cs = Vec::from_iter(lin_term.steps[i].1.iter().map(|i| &ivalues[*i]));
            let value = eval_op(&lin_term.steps[i].0, &cs, &env);
            ivalues[i] = value;
        }
        let val = ivalues.last().unwrap().clone();
        if val == Value::Bool(true) {
            for (var, val) in &env {
                eprintln!("{}: {}", var, val);
            }
            println!("sat");
            return Ok(());
        }
    }
    println!("unsat");
    Ok(())
}
