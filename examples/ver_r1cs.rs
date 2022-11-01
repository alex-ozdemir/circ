use circ::ir::term::text::*;
use circ::target::r1cs::trans2 as trans;
use circ::target::smt::find_model;
use circ::util::field::DFL_T;
use structopt::{clap::arg_enum, StructOpt};

#[derive(Debug, StructOpt)]
#[structopt(name = "ver_r1cs", about = "Verifier for CirC's R1CS lowering pass")]
struct Options {
    #[structopt(long)]
    max_args: usize,

    #[structopt(long, short)]
    properties: Vec<Prop>,

    #[structopt(long, short)]
    ops: Vec<String>,

    #[structopt(long, short, possible_values = &["bool", "bitvector"])]
    sorts: Vec<String>,
}

arg_enum! {
    /// A verifiable property: 'sound' or 'complete'
    #[derive(Debug, PartialEq, Eq, Clone)]
    enum Prop {
        Sound,
        Complete,
    }
}

impl Prop {
    fn failure_message(&self) -> &'static str {
        match self {
            Self::Sound => "unsound",
            Self::Complete => "incomplete",
        }
    }
}

fn main() -> Result<(), String> {
    env_logger::Builder::from_default_env()
        .format_level(false)
        .format_timestamp(None)
        .init();
    let opts = dbg!(Options::from_args());
    let props = if opts.properties.is_empty() {
        vec![Prop::Sound, Prop::Complete]
    } else {
        opts.properties.clone()
    };
    let bnd = trans::ver::Bound {
        args: opts.max_args,
        bv_bits: 4,
    };

    for r in trans::boolean::rules() {
        let op_ok = opts.ops.is_empty() || opts.ops.contains(&format!("{}", r.pattern().0));
        let sort_ok = opts.sorts.is_empty() || opts.sorts.contains(&format!("{}", r.pattern().0));
        if op_ok && sort_ok {
            for prop in &props {
                let f = match prop {
                    Prop::Sound => trans::ver::soundness_terms,
                    //Prop::Complete => trans::ver::completeness_terms,
                    Prop::Complete => unimplemented!(),
                };
                for (t, soundness) in f(&r, &bnd, &DFL_T) {
                    println!("check: {}", t);
                    if let Some(model) = find_model(&soundness) {
                        println!("ERROR: {}", prop.failure_message());
                        println!(
                            "Formula:\n{}\n",
                            pp_sexpr(serialize_term(&soundness).as_bytes(), 100)
                        );
                        println!(
                            "Counterexample: {}",
                            serialize_value_map(&model.into_iter().collect())
                        );
                        return Err(format!("ERROR: {}", prop.failure_message()));
                    }
                }
            }
        }
    }
    Ok(())
}
