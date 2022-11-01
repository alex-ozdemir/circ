use circ::ir::term::text::*;
use circ::target::r1cs::trans2 as trans;
use circ::target::smt::find_model;
use circ::util::field::DFL_T;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(name = "ver_r1cs", about = "Verifier for CirC's R1CS lowering pass")]
struct Options {
    #[structopt(long)]
    max_args: usize,
}

fn main() -> Result<(), String> {
    env_logger::Builder::from_default_env()
        .format_level(false)
        .format_timestamp(None)
        .init();
    let opts = Options::from_args();
    let bnd = trans::ver::Bound {
        args: opts.max_args,
        bv_bits: 4,
    };

    for r in trans::boolean::rules() {
        println!("Rule for {:?}", r.pattern());
        for (t, soundness) in trans::ver::bool_soundness_terms(&r, &bnd, &DFL_T) {
            println!("check: {}", t);
            if let Some(model) = find_model(&soundness) {
                println!("UNSOUND");
                println!(
                    "Formula:\n{}\n",
                    pp_sexpr(serialize_term(&soundness).as_bytes(), 100)
                );
                println!(
                    "Counterexample: {}",
                    serialize_value_map(&model.into_iter().collect())
                );
                return Err("UNSOUND".into());
            }
        }
    }
    Ok(())
}
