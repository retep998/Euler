#include <cstdint>
#include <functional>
#include <chrono>
#include <iostream>

void test(std::function<uint64_t()> func, uint64_t count) {
    uint64_t r {};
    std::chrono::high_resolution_clock::time_point a {std::chrono::high_resolution_clock::now()};
    for (uint64_t i = count; i; --i) r = func();
    std::chrono::high_resolution_clock::time_point b {std::chrono::high_resolution_clock::now()};
    std::cout << "Time: " << static_cast<double>(std::chrono::duration_cast<std::chrono::nanoseconds>(b - a).count()) / count << " ns" << std::endl;
    std::cout << "Result: " << r << std::endl;
}

uint64_t p15() {
    volatile unsigned arg {20};
    unsigned size {arg};
    double n {1}, d {1}, nn {static_cast<double>(size)}, dd {0};
    for (unsigned i {size}; i; --i) {
        nn += 1, dd += 1;
        n *= nn, d *= dd;
    }
    return static_cast<uint64_t>(n / d);
}
int main() {
    test(p15, 100000000);
    return 0;
}