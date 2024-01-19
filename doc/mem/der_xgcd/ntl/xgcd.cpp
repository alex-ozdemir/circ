#include <cassert>
#include <chrono>
#include <ostream>
#include <stdint.h>
#include <string>
#include <time.h>
#include <vector>

#include <NTL/BasicThreadPool.h>
#include <NTL/ZZ.h>
#include <NTL/ZZ_p.h>
#include <NTL/ZZ_pX.h>
#include <NTL/vec_ZZ_p.h>

#include "flint/fmpz.h"
#include "flint/fmpz_mod.h"
#include "flint/fmpz_mod_poly.h"
#include "flint/fmpz_vec.h"

void usage(char* argv[])
{
  std::cerr << "USAGE " << argv[0] << " (ntl-feea|flint-feea|ntl-interp) LOG2_NUM_ROOTS [NUM_THREADS]" << std::endl;
  exit(1);
}

enum class Mode {
  NtlFeea,
  NtlMul,
  FlintFeea,
  NtlInterp,
};

Mode parse_mode(char* argv[], const std::string& mode)
{
  if (mode == "ntl-feea") {
    return Mode::NtlFeea;
  } else if (mode == "flint-feea") {
    return Mode::FlintFeea;
  } else if (mode == "ntl-mul") {
    return Mode::NtlMul;
  } else if (mode == "ntl-interp") {
    return Mode::NtlInterp;
  } else {
    std::cerr << "Unknown mode string " << mode << std::endl;
    usage(argv);
    // silence warning with dead code
    return Mode::NtlInterp;
  }
}

// returns 0 if error (some 0)
int batch_inv(NTL::vec_ZZ_p& xs)
{
  size_t n = xs.length();
  NTL::vec_ZZ_p ps;
  ps.SetLength(n);
  bool error = false;
  NTL::ZZ_pContext ctx;
  ctx.save();
  NTL_EXEC_RANGE(n, first, last)
  {
    ctx.restore();
    ps[first] = xs[first];
    for (long i = first; i + 1 < last; ++i) {
      NTL::mul(ps[i + 1], xs[i + 1], ps[i]);
    }
    if (ps[last - 1] == 0)
      error = true;
    NTL::inv(ps[last - 1], ps[last - 1]);
    NTL::ZZ_p t;
    for (long i = last - 2; i < last && i >= first; --i) {
      NTL::mul(t, ps[i + 1], xs[i + 1]);
      NTL::mul(xs[i + 1], ps[i + 1], ps[i]);
      ps[i] = t;
    }
    xs[first] = ps[first];
  }
  NTL_EXEC_RANGE_END
  ps.SetLength(0);
  return !error;
}

void tree_mul(std::vector<NTL::ZZ_pX>& tree, const NTL::vec_ZZ_p& a)
{
  const size_t n = a.length();
  assert((n & (n - 1)) == 0);
  assert(tree.empty());
  for (size_t i = 0; i < n; ++i) {
    NTL::ZZ_p na;
    NTL::negate(na, a[i]);
    tree.emplace_back();
    NTL::SetX(tree.back());
    NTL::SetCoeff(tree.back(), 0, na);
  }
  for (size_t next_level_size = n / 2; next_level_size != 0; next_level_size /= 2) {
    size_t prev_i = tree.size() - 2 * next_level_size;
    long level_start = tree.size();
    tree.resize(level_start + next_level_size);
    NTL::ZZ_pContext ctx;
    ctx.save();
    NTL_EXEC_RANGE(next_level_size, start, end)
    {
      ctx.restore();
      for (long i = start; i < end; ++i) {
        assert(prev_i + 2 * i < tree.size());
        assert(prev_i + 2 * i + 1 < tree.size());
        NTL::mul(tree[level_start + i], tree[prev_i + 2 * i], tree[prev_i + 2 * i + 1]);
      }
    }
    NTL_EXEC_RANGE_END
  }
  assert(2 * n == tree.size() + 1);
}

void tree_eval(NTL::vec_ZZ_p& b, const NTL::ZZ_pX& f, const std::vector<NTL::ZZ_pX>& tree)
{
  const size_t ts = tree.size();
  const size_t n = (ts + 1) / 2;
  assert((n & (n - 1)) == 0);
  std::vector<NTL::ZZ_pX> qs { f % tree.back() };
  for (size_t lev_size = 2; lev_size <= n; lev_size *= 2) {
    const size_t lev_start = qs.size();
    qs.resize(lev_start + lev_size);
    NTL::ZZ_pContext ctx;
    ctx.save();
    NTL_EXEC_RANGE(lev_size, first, last)
    {
      ctx.restore();
      for (size_t i = lev_start + first; i < lev_start + last; ++i) {
        NTL::rem(qs[i], qs[(i - 1) / 2], tree[ts - i - 1]);
      }
    }
    NTL_EXEC_RANGE_END
  }
  b.SetLength(n);
  NTL_EXEC_RANGE(n, first, last)
  {
    for (long i = first; i < last; ++i) {
      assert(NTL::deg(qs[ts - 1 - i]) == 0);
      b[i] = NTL::ConstTerm(qs[ts - 1 - i]);
    }
  }
  NTL_EXEC_RANGE_END
}

void tree_combine(NTL::ZZ_pX& f, const NTL::vec_ZZ_p& b, const std::vector<NTL::ZZ_pX>& tree)
{
  const size_t ts = tree.size();
  const size_t n = (ts + 1) / 2;
  assert((n & (n - 1)) == 0);
  assert(b.length() == static_cast<long>(n));
  assert(ts == 2 * n - 1);
  std::vector<NTL::ZZ_pX> cs {};
  for (size_t i = 0; i < n; ++i) {
    cs.emplace_back(b[i]);
  }
  for (
      size_t lev_width = n / 2,
             stride = 1,
             coeff_start = 0;
      lev_width > 0;
      coeff_start += 2 * lev_width,
             stride *= 2,
             lev_width /= 2) {
    NTL::ZZ_pContext ctx;
    ctx.save();
    NTL_EXEC_RANGE(lev_width, first, last)
    {
      ctx.restore();
      for (long i = first; i < last; i++) {
        NTL::ZZ_pX& left = cs[2 * i * stride];
        NTL::ZZ_pX& right = cs[(2 * i + 1) * stride];
        const NTL::ZZ_pX& left_coeff = tree[coeff_start + 2 * i];
        const NTL::ZZ_pX& right_coeff = tree[coeff_start + 2 * i + 1];
        NTL::mul(left, left, right_coeff);
        NTL::mul(right, right, left_coeff);
        NTL::add(left, left, right);
      }
    }
    NTL_EXEC_RANGE_END
  }
  f = std::move(cs[0]);
}

int main(int argc, char* argv[])
{
  if (argc < 3) {
    usage(argv);
  }
  Mode mode = parse_mode(argv, argv[1]);
  size_t n = 1 << std::stoi(argv[2]);
  size_t threads = 1;
  if (argc == 4) {
    threads = std::stoi(argv[3]);
  }
  std::cerr << " degree: " << n << std::endl;
  std::cerr << "threads: " << threads << std::endl;

  std::chrono::steady_clock::time_point begin, end, bbegin, eend;
  switch (mode) {
  case Mode::NtlMul: {
    NTL::SetNumThreads(threads);
    NTL::ZZ p = NTL::to_ZZ("52435875175126190479447740508185965837690552500527637822603658699938581184513");
    NTL::ZZ_p::init(p);

    NTL::ZZ_pX a = NTL::random_ZZ_pX(n);
    NTL::ZZ_pX b = NTL::random_ZZ_pX(n);
    NTL::ZZ_pX c = a * b;
    break;
  }
  case Mode::FlintFeea: {
    flint_set_num_threads(threads);
    fmpz_t p;
    fmpz_init(p);
    fmpz_set_str(p, "52435875175126190479447740508185965837690552500527637822603658699938581184513", 10);
    fmpz_mod_ctx_t ctx;
    fmpz_mod_ctx_init(ctx, p);

    std::cerr << " degree: " << n << std::endl;
    std::cerr << "threads: " << threads << std::endl;

    flint_rand_t rng;
    flint_randinit(rng);

    fmpz* roots = _fmpz_vec_init(n);
    for (size_t i = 0; i < n; ++i) {
      fmpz_randm(&roots[i], rng, p);
    }

    bbegin = std::chrono::steady_clock::now();
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
    eend = std::chrono::steady_clock::now();
    std::cerr << " XGCD  time (per d) = " << static_cast<double>(std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count()) / n / 1e3 << std::endl;
    std::cerr << "total  time (per d) = " << static_cast<double>(std::chrono::duration_cast<std::chrono::nanoseconds>(eend - bbegin).count()) / n / 1e3 << std::endl;

    if (!fmpz_mod_poly_is_one(g, ctx)) {
      std::cerr << "non-one GCD: " << fmpz_mod_poly_get_str(g, ctx) << std::endl;
      return 1;
    }
    break;
  }
  case Mode::NtlFeea: {
    NTL::SetNumThreads(threads);
    NTL::ZZ p = NTL::to_ZZ("52435875175126190479447740508185965837690552500527637822603658699938581184513");
    NTL::ZZ_p::init(p);

    NTL::vec_ZZ_p roots;
    NTL::random(roots, n);

    NTL::ZZ_pX g, s, t;
    bbegin = std::chrono::steady_clock::now();
    begin = std::chrono::steady_clock::now();
    NTL::ZZ_pX f = NTL::BuildFromRoots(roots);
    end = std::chrono::steady_clock::now();
    std::cerr << "interp time (per d) = " << static_cast<double>(std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count()) / n / 1e3 << std::endl;

    begin = std::chrono::steady_clock::now();
    NTL::ZZ_pX df = NTL::diff(f);
    end = std::chrono::steady_clock::now();
    std::cerr << "deriv  time (per d) = " << static_cast<double>(std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count()) / n / 1e3 << std::endl;

    begin = std::chrono::steady_clock::now();
    NTL::XGCD(g, s, t, f, df);
    end = std::chrono::steady_clock::now();
    eend = std::chrono::steady_clock::now();
    std::cerr << "XGCD   time (per d) = " << static_cast<double>(std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count()) / n / 1e3 << std::endl;
    std::cerr << "total  time (per d) = " << static_cast<double>(std::chrono::duration_cast<std::chrono::nanoseconds>(eend - bbegin).count()) / n / 1e3 << std::endl;
    assert(g == s * f + t * df);
    break;
  }
  case Mode::NtlInterp: {
    NTL::SetNumThreads(threads);
    NTL::ZZ p = NTL::to_ZZ("52435875175126190479447740508185965837690552500527637822603658699938581184513");
    NTL::ZZ_p::init(p);

    NTL::vec_ZZ_p roots;
    NTL::random(roots, n);

    std::chrono::steady_clock::time_point begin, end, bbegin, eend;

    NTL::ZZ_pX g, s, t;
    std::vector<NTL::ZZ_pX> tree;

    bbegin = std::chrono::steady_clock::now();
    begin = std::chrono::steady_clock::now();
    tree_mul(tree, roots);
    NTL::ZZ_pX f = tree.back();
    // NTL::ZZ_pX f = NTL::BuildFromRoots(roots);
    end = std::chrono::steady_clock::now();
    std::cerr << "interp time (per d) = " << static_cast<double>(std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count()) / n / 1e3 << std::endl;

    begin = std::chrono::steady_clock::now();
    NTL::ZZ_pX df = NTL::diff(f);
    end = std::chrono::steady_clock::now();
    std::cerr << "deriv  time (per d) = " << static_cast<double>(std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count()) / n / 1e3 << std::endl;

    begin = std::chrono::steady_clock::now();
    NTL::vec_ZZ_p df_vals;
    // eval(df_vals, df, roots);
    tree_eval(df_vals, df, tree);
    end = std::chrono::steady_clock::now();
    std::cerr << "eval   time (per d) = " << static_cast<double>(std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count()) / n / 1e3 << std::endl;

    begin = std::chrono::steady_clock::now();
    assert(batch_inv(df_vals));
    //  for (size_t i = 0; i < n; ++i) {
    //    df_vals[i] = NTL::inv(df_vals[i]);
    //  }
    end = std::chrono::steady_clock::now();
    std::cerr << "invert time (per d) = " << static_cast<double>(std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count()) / n / 1e3 << std::endl;

    begin = std::chrono::steady_clock::now();
    for (size_t i = 0; i < n; ++i) {
      df_vals[i] = NTL::sqr(df_vals[i]);
    }
    NTL::ZZ_pX deriv_inv;
    tree_combine(deriv_inv, df_vals, tree);
    end = std::chrono::steady_clock::now();
    std::cerr << "interp time (per d) = " << static_cast<double>(std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count()) / n / 1e3 << std::endl;

    begin = std::chrono::steady_clock::now();
    t = deriv_inv;
    assert(NTL::divide(s, 1 - df * t, f));
    end = std::chrono::steady_clock::now();
    eend = std::chrono::steady_clock::now();
    std::cerr << "div    time (per d) = " << static_cast<double>(std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count()) / n / 1e3 << std::endl;
    std::cerr << "total  time (per d) = " << static_cast<double>(std::chrono::duration_cast<std::chrono::nanoseconds>(eend - bbegin).count()) / n / 1e3 << std::endl;

    g = s * f + t * df;
    assert(g == 1);
    break;
  }
  }
  return 0;
}

