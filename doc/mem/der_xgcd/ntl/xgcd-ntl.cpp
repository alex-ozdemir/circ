#include <NTL/ZZ.h>
#include <NTL/ZZ_p.h>
#include <NTL/ZZ_pX.h>
#include <NTL/vec_ZZ_p.h>
#include <NTL/BasicThreadPool.h>
#include <chrono>
#include <ostream>
#include <stdint.h>
#include <time.h>

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
    NTL::SetNumThreads(threads);
  }
  NTL::ZZ p = NTL::to_ZZ("52435875175126190479447740508185965837690552500527637822603658699938581184513");
  NTL::ZZ_p::init(p);
  std::cerr << " degree: " << n << std::endl;
  std::cerr << "threads: " << threads << std::endl;
  std::cerr << "      p: " << p << std::endl;

  NTL::vec_ZZ_p roots;
  NTL::random(roots, n);

  std::chrono::steady_clock::time_point begin, end;

  begin = std::chrono::steady_clock::now();
  NTL::ZZ_pX f = NTL::BuildFromRoots(roots);
  end = std::chrono::steady_clock::now();
  std::cerr << "interp time (per d) = " << static_cast<double>(std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count()) / n / 1e3 << std::endl;

  begin = std::chrono::steady_clock::now();
  NTL::ZZ_pX df = NTL::diff(f);
  end = std::chrono::steady_clock::now();
  std::cerr << "deriv  time (per d) = " << static_cast<double>(std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count()) / n / 1e3 << std::endl;
  NTL::ZZ_pX g, s, t;

  begin = std::chrono::steady_clock::now();
  NTL::XGCD(g, s, t, f, df);
  end = std::chrono::steady_clock::now();
  std::cerr << " XGCD  time = " << static_cast<double>(std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count()) / 1e9 << "s" << std::endl;
  std::cerr << " XGCD  time = " << static_cast<double>(std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count()) / n / 1e3 << "us/elem" << std::endl;

  if (g != 1) {
    std::cerr << "non-one GCD: " << g << std::endl;
    return 1;
  }

  return 0;
}

