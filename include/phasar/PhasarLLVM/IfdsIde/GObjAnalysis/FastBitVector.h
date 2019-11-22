#ifndef FASTBITVECTOR
#define FASTBITVECTOR

#include <llvm/Support/MathExtras.h>

namespace psr {

template<int N=2> class FastBitVector {
  static_assert(N > 0, "Positive number of words");
  uint64_t bv[N];
  static const unsigned bitwidth = 8 * sizeof(uint64_t);
  int find_first(int start) const {
    for (int i = start; i < N; ++i) {
      int j = llvm::countTrailingZeros(bv[i]);
      if (j != bitwidth)
        return j + i * bitwidth;
    }
    return -1;
  }

public:
  FastBitVector() {
    for (unsigned i = 0; i < N; ++i)
      bv[i] = 0;
  }
  FastBitVector(unsigned size, bool v = false) {
    for (unsigned i = 0; i < N; ++i)
      bv[i] = 0;
    if (v) {
      for (unsigned i = 0; i < size; ++i) {
        set(i, true);
      }
    }
  }

  FastBitVector &operator=(const FastBitVector &other) = default;
  FastBitVector(const FastBitVector &other) = default;

  void set(int bit, bool v = true) {
    assert(0 <= bit);
    assert(bit < (int) (N * bitwidth));
    unsigned wordIndex = bit / bitwidth;
    unsigned i = bit % bitwidth;
    uint64_t &word = bv[wordIndex];
    if (v) {
      word |= ((uint64_t)1 << i);
    } else {
      word &= ~((uint64_t)1 << i);
    }
  }

  bool get(int bit) const {
    unsigned wordIndex = bit / bitwidth;
    unsigned i = bit % bitwidth;
    return ((uint64_t) 1 << i) & bv[wordIndex];
  }

  int find_first() const {
    return find_first(0);
  }

  int find_next(int i) const {
    assert(0 <= i);
    assert(i < (int) (N * bitwidth));
    unsigned wordIndex = i / bitwidth;
    unsigned j = i % bitwidth;
    if (j == bitwidth - 1)
      return find_first(wordIndex + 1);
    uint64_t word = bv[wordIndex];
    uint64_t mask = ~(((uint64_t)(1) << (j+1)) - 1);
    if ((word & mask) == 0)
      return find_first(wordIndex + 1);
    return wordIndex * bitwidth + llvm::countTrailingZeros(word & mask);
  }

  FastBitVector operator|(const FastBitVector &rhs) const {
    FastBitVector r;
    for (int i = 0; i < N; ++i)
      r.bv[i] = bv[i] | rhs.bv[i];
    return r;
  }

  bool operator==(const FastBitVector &rhs) const {
    for (int i = 0; i < N; ++i)
      if (bv[i] != rhs.bv[i])
        return false;
    return true;
  }

  bool operator<(const FastBitVector &rhs) const {
    for (int i = N-1; i >= 0; --i) {
      if (bv[i] > rhs.bv[i])
        return false;
      if (bv[i] < rhs.bv[i])
        return true;
    }
    return false;
  }

  bool isAllZeros() const {
    for (int i = 0; i < N; i++)
      if (bv[i] != 0ull)
        return false;
    return true;
  }
};

} // end namespace psr
#endif
