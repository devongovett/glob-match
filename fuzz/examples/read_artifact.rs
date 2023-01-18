use arbitrary::{Arbitrary, Unstructured};
use fuzz_local::Data;

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
  let mut args = std::env::args().into_iter();
  args
    .next()
    .expect("The first argument should be the file path.");

  let target = args
    .next()
    .expect("Must specify a fuzz target for the artifact.");

  match target.as_str() {
    "both_fuzz" => {
      let name = args
        .next()
        .expect("The fuzz artifact name must be specified.");

      let bytes = std::fs::read(format!("artifacts/both_fuzz/{name}"))?;

      println!("{:?}", Data::arbitrary(&mut Unstructured::new(&bytes))?);
    }
    "pattern_on_itself" => {
      let name = args
        .next()
        .expect("The fuzz artifact name must be specified.");

      let bytes = std::fs::read(format!("artifacts/pattern_on_itself/{name}"))?;

      println!("{:?}", String::from_utf8(bytes));
    }
    target => {
      panic!("The target name '{target}' is invalid.");
    }
  }

  Ok(())
}
