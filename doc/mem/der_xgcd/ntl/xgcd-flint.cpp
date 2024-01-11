#include "flint/fmpz.h"
#include "flint/fmpz_mod.h"
#include "flint/fmpz_mod_poly.h"
#include "flint/fmpz_vec.h"
#include <chrono>
#include <iostream>
#include <ostream>
#include <stdint.h>
#include <time.h>
#include <vector>

int main(int argc, char* argv[])
{
  if (argc < 2) {
    std::cerr << "USAGE " << argv[0] << " LOG2_NUM_ROOTS [NUM_THREADS]" << std::endl;
    return 1;
  }
  size_t n = 1 << std::stoi(argv[1]);
  size_t threads = 1;
  if (argc == 3) {
    threads = std::stoi(argv[2]);
    flint_set_num_threads(threads);
  }
  fmpz_t p;
  fmpz_init(p);
  fmpz_set_str(p, "52435875175126190479447740508185965837690552500527637822603658699938581184513", 10);
  fmpz_mod_ctx_t ctx;
  fmpz_mod_ctx_init(ctx, p);

  std::cerr << " degree: " << n << std::endl;
  std::cerr << "threads: " << threads << std::endl;
  std::cerr << "      p: " << p << std::endl;

  flint_rand_t rng;
  flint_randinit(rng);

  fmpz* roots = _fmpz_vec_init(n);
  for (size_t i = 0; i < n; ++i) {
    fmpz_randm(&roots[i], rng, p);
  }

  std::chrono::steady_clock::time_point begin, end;

  begin = std::chrono::steady_clock::now();
  fmpz_mod_poly_t f;
  fmpz_mod_poly_init(f, ctx);
  fmpz_mod_poly_product_roots_fmpz_vec(f, roots, n, ctx);
  end = std::chrono::steady_clock::now();
  std::cerr << "interp time (per d) = " << static_cast<double>(std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count()) / n / 1e3 << std::endl;

  begin = std::chrono::steady_clock::now();
  fmpz_mod_poly_t df;
  fmpz_mod_poly_init(df, ctx);
  fmpz_mod_poly_derivative(df, f, ctx);
  end = std::chrono::steady_clock::now();
  std::cerr << "deriv  time (per d) = " << static_cast<double>(std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count()) / n / 1e3 << std::endl;
  fmpz_mod_poly_t g, s, t;
  fmpz_mod_poly_init(g, ctx);
  fmpz_mod_poly_init(s, ctx);
  fmpz_mod_poly_init(t, ctx);

  begin = std::chrono::steady_clock::now();
  fmpz_mod_poly_xgcd(g, s, t, f, df, ctx);
  end = std::chrono::steady_clock::now();
  std::cerr << " XGCD  time = " << static_cast<double>(std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count()) / 1e9 << "s" << std::endl;
  std::cerr << " XGCD  time = " << static_cast<double>(std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count()) / n / 1e3 << "us/elem" << std::endl;

  if (!fmpz_mod_poly_is_one(g, ctx)) {
    std::cerr << "non-one GCD: " << fmpz_mod_poly_get_str(g, ctx) << std::endl;
    return 1;
  }

  return 0;
}
