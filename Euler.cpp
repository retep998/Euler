#include <iostream>
#include <cmath>
#include <cstdint>
#include <memory>
#include <vector>
#include <chrono>
#include <thread>
#include <string>
#include <algorithm>
#include <array>
#include <numeric>
#include <fstream>
using namespace std;
using namespace std::chrono;
using namespace std::this_thread;

#define WIN32_LEAN_AND_MEAN
#define VC_EXTRALEAN
#define NOMINMAX
#include <Windows.h>


void test_win_rep(std::function<uint64_t()> func, uint64_t count) {
    uint64_t r;
    LARGE_INTEGER f, b, e;
    QueryPerformanceFrequency(&f);
    QueryPerformanceCounter(&b);
    for (uint64_t i = count; i; --i) r = func();
    QueryPerformanceCounter(&e);
    cout << "Time: " << (e.QuadPart - b.QuadPart) * 1000000000. / f.QuadPart / count << " ns" << endl;
    cout << "Result: " << r << endl;
}

void test_win(std::function<uint64_t()> func) {
    LARGE_INTEGER f, b, e;
    QueryPerformanceFrequency(&f);
    QueryPerformanceCounter(&b);
    uint64_t r = func();
    QueryPerformanceCounter(&e);
    cout << "Time: " << (e.QuadPart - b.QuadPart) * 1000000000. / f.QuadPart << " ns" << endl;
    cout << "Result: " << r << endl;
}

void test_rep(std::function<uint64_t()> func, uint64_t count) {
    uint64_t r;
    auto a = high_resolution_clock::now();
    for (uint64_t i = count; i; --i) r = func();
    auto b = high_resolution_clock::now();
    cout << "Time: " << static_cast<double>(duration_cast<nanoseconds>(b-a).count()) / count << " ns" << endl;
    cout << "Result: " << r << endl;
}
vector<bool> make_sieve(uint64_t s) {
    vector<bool> sieve(s);
    uint64_t ss = static_cast<uint64_t>(sqrt(s) + 1);
    for (uint64_t i = 2; i < ss; ++i) {
        for (uint64_t j = i * i; j < s; j += i) {
            sieve[j] = true;
        }
    }
    return sieve;
}
uint64_t p1() {
    uint64_t n = 1000;
    --n;
    uint64_t n3 = n / 3;
    n3 = n3 * (n3 + 1) * 3 / 2;
    uint64_t n5 = n / 5;
    n5 = n5 * (n5 + 1) * 5 / 2;
    uint64_t n15 = n / 15;
    n15 = n15 * (n15 + 1) * 15 / 2;
    return n3 + n5 - n15;
}
uint64_t p2() {
    uint64_t s = 0;
    uint64_t n1 = 1;
    uint64_t n2 = 1;
    uint64_t n3 = 2;
    while (n3 <= 4000000) {
        s += n3;
        n1 = n2 + n3;
        n2 = n3 + n1;
        n3 = n1 + n2;
    }
    return s;
}
uint64_t p3() {
    uint64_t n = 600851475143;
    uint64_t s = static_cast<uint64_t>(sqrt(n) + 1);
    auto sieve(make_sieve(s));
    for (uint64_t i = 2; i < s; ++i) {
        if (!sieve[i]) for (;;) {
            uint64_t d = n / i;
            uint64_t r = n % i;
            if (r != 0) break;
            n = d;
            s = static_cast<uint64_t>(sqrt(n) + 1);
        }
    }
    return n;
}
uint64_t p4() {
    char buf[0x10];
    uint32_t best = 0;
    for (uint32_t i = 999; i >= 100; --i) {
        for (uint32_t j = 999; j >= i; --j) {
            uint32_t p = i * j;
            if (p <= best) continue;
            int n = sprintf_s(buf, "%u", p);
            bool found = true;
            for (int m = 0; m < n >> 1; ++m) {
                if (buf[n - m - 1] != buf[m]) {
                    found = false;
                    break;
                }
            }
            if (found) best = p;
        }
    }
    return best;
}
uint64_t p5() {
    uint32_t s = 20;
    auto sieve(make_sieve(s));
    uint8_t buf[21] = {};
    for (uint8_t i = 2; i <= s; ++i) {
        for (uint8_t n = i, j = 2; n != 1; ++j) {
            if (!sieve[j]) {
                uint8_t c = 0;
                for (;;) {
                    uint8_t d = n / j;
                    uint8_t r = n % j;
                    if (r != 0) break;
                    n = d;
                    ++c;
                }
                if (buf[j] < c) buf[j] = c;
            }
        }
    }
    uint32_t r = 1;
    for (uint8_t i = 1; i <= s; ++i) {
        for (uint8_t j = buf[i]; j; --j) {
            r *= i;
        }
    }
    return r;
}
uint64_t p6() {
    uint64_t s1 = 0, s2 = 0;
    for (uint64_t i = 1; i <= 100; ++i) {
        s1 += i * i;
        s2 += i;
    }
    uint64_t d = s2 * s2 - s1;
    return d;
}
uint64_t p7() {
    uint64_t s = 10001;
    auto sieve(make_sieve(104744));
    for (uint64_t i = 2, n = 0;; ++i) {
        if (!sieve[i]) {
            if (++n == s) {
                return i;
            }
        }
    }
}
uint64_t p8() {
    char s[] = "7316717653133062491922511967442657474235534919493496983520312774506326239578318016984801869478851843858615607891129494954595017379583319528532088055111254069874715852386305071569329096329522744304355766896648950445244523161731856403098711121722383113622298934233803081353362766142828064444866452387493035890729629049156044077239071381051585930796086670172427121883998797908792274921901699720888093776657273330010533678812202354218097512545405947522435258490771167055601360483958644670632441572215539753697817977846174064955149290862569321978468622482839722413756570560574902614079729686524145351004748216637048440319989000889524345065854122758866688116427171479924442928230863465674813919123162824586178664583591245665294765456828489128831426076900422421902267105562632111110937054421750694165896040807198403850962455444362981230987879927244284909188845801561660979191338754992005240636899125607176060588611646710940507754100225698315520005593572972571636269561882670428252483600823257530420752963450";
    uint8_t n[1000];
    for (uint16_t i = 0; i < 1000; ++i) {
        n[i] = s[i] - '0';
    }
    uint32_t b = 0;
    for (uint16_t i = 0; i < 996; ++i) {
        uint32_t p = n[i + 0] * n[i + 1] * n[i + 2] * n[i + 3] * n[i + 4];
        if (p > b) b = p;
    }
    return b;
}
uint64_t p9() {
    for (uint32_t a = 1; a < 1000; ++a) for (uint32_t b = a; b < 1000; ++b) {
        uint32_t c = 1000 - a - b;
        if (a * a + b * b == c * c) return a * b * c;
    }
    return 0;
}
uint64_t p10() {
    auto sieve(make_sieve(2000000));
    uint64_t s = 0;
    for (uint64_t i = 2; i < 2000000; ++i) {
        if (!sieve[i]) {
            s += i;
        }
    }
    return s;
}
uint64_t p11() {
    uint8_t const a[20][20] = {
        8, 2, 22, 97, 38, 15, 0, 40, 0, 75, 4, 5, 7, 78, 52, 12, 50, 77, 91, 8,
        49, 49, 99, 40, 17, 81, 18, 57, 60, 87, 17, 40, 98, 43, 69, 48, 4, 56, 62, 0,
        81, 49, 31, 73, 55, 79, 14, 29, 93, 71, 40, 67, 53, 88, 30, 3, 49, 13, 36, 65,
        52, 70, 95, 23, 4, 60, 11, 42, 69, 24, 68, 56, 1, 32, 56, 71, 37, 2, 36, 91,
        22, 31, 16, 71, 51, 67, 63, 89, 41, 92, 36, 54, 22, 40, 40, 28, 66, 33, 13, 80,
        24, 47, 32, 60, 99, 3, 45, 2, 44, 75, 33, 53, 78, 36, 84, 20, 35, 17, 12, 50,
        32, 98, 81, 28, 64, 23, 67, 10, 26, 38, 40, 67, 59, 54, 70, 66, 18, 38, 64, 70,
        67, 26, 20, 68, 2, 62, 12, 20, 95, 63, 94, 39, 63, 8, 40, 91, 66, 49, 94, 21,
        24, 55, 58, 5, 66, 73, 99, 26, 97, 17, 78, 78, 96, 83, 14, 88, 34, 89, 63, 72,
        21, 36, 23, 9, 75, 0, 76, 44, 20, 45, 35, 14, 0, 61, 33, 97, 34, 31, 33, 95,
        78, 17, 53, 28, 22, 75, 31, 67, 15, 94, 3, 80, 4, 62, 16, 14, 9, 53, 56, 92,
        16, 39, 5, 42, 96, 35, 31, 47, 55, 58, 88, 24, 0, 17, 54, 24, 36, 29, 85, 57,
        86, 56, 0, 48, 35, 71, 89, 7, 5, 44, 44, 37, 44, 60, 21, 58, 51, 54, 17, 58,
        19, 80, 81, 68, 5, 94, 47, 69, 28, 73, 92, 13, 86, 52, 17, 77, 4, 89, 55, 40,
        4, 52, 8, 83, 97, 35, 99, 16, 7, 97, 57, 32, 16, 26, 26, 79, 33, 27, 98, 66,
        88, 36, 68, 87, 57, 62, 20, 72, 3, 46, 33, 67, 46, 55, 12, 32, 63, 93, 53, 69,
        4, 42, 16, 73, 38, 25, 39, 11, 24, 94, 72, 18, 8, 46, 29, 32, 40, 62, 76, 36,
        20, 69, 36, 41, 72, 30, 23, 88, 34, 62, 99, 69, 82, 67, 59, 85, 74, 4, 36, 16,
        20, 73, 35, 29, 78, 31, 90, 1, 74, 31, 49, 71, 48, 86, 81, 16, 23, 57, 5, 54,
        1, 70, 54, 71, 83, 51, 54, 69, 16, 92, 33, 48, 61, 43, 52, 1, 89, 19, 67, 48};
    uint32_t max = 0;
    for (uint8_t x = 0; x <= 16; ++x) {
        for (uint8_t y = 0; y <= 16; ++y) {
            uint32_t n = a[x][y] * a[x + 1][y + 1] * a[x + 2][y + 2] * a[x + 3][y + 3];
            if (n > max) max = n;
            uint32_t m = a[x + 3][y] * a[x + 2][y + 1] * a[x + 1][y + 2] * a[x][y + 3];
            if (m > max) max = m;
        }
    }
    for (uint8_t x = 0; x < 20; ++x) {
        for (uint8_t y = 0; y <= 16; ++y) {
            uint32_t n = a[x][y] * a[x][y + 1] * a[x][y + 2] * a[x][y + 3];
            if (n > max) max = n;
            uint32_t m = a[y][x] * a[y + 1][x] * a[y + 2][x] * a[y + 3][x];
            if (m > max) max = m;
        }
    }
    return max;
}
uint64_t p12() {
    return 0;
}
uint64_t p13() {
    string d[100] = {
        "37107287533902102798797998220837590246510135740250",
        "46376937677490009712648124896970078050417018260538",
        "74324986199524741059474233309513058123726617309629",
        "91942213363574161572522430563301811072406154908250",
        "23067588207539346171171980310421047513778063246676",
        "89261670696623633820136378418383684178734361726757",
        "28112879812849979408065481931592621691275889832738",
        "44274228917432520321923589422876796487670272189318",
        "47451445736001306439091167216856844588711603153276",
        "70386486105843025439939619828917593665686757934951",
        "62176457141856560629502157223196586755079324193331",
        "64906352462741904929101432445813822663347944758178",
        "92575867718337217661963751590579239728245598838407",
        "58203565325359399008402633568948830189458628227828",
        "80181199384826282014278194139940567587151170094390",
        "35398664372827112653829987240784473053190104293586",
        "86515506006295864861532075273371959191420517255829",
        "71693888707715466499115593487603532921714970056938",
        "54370070576826684624621495650076471787294438377604",
        "53282654108756828443191190634694037855217779295145",
        "36123272525000296071075082563815656710885258350721",
        "45876576172410976447339110607218265236877223636045",
        "17423706905851860660448207621209813287860733969412",
        "81142660418086830619328460811191061556940512689692",
        "51934325451728388641918047049293215058642563049483",
        "62467221648435076201727918039944693004732956340691",
        "15732444386908125794514089057706229429197107928209",
        "55037687525678773091862540744969844508330393682126",
        "18336384825330154686196124348767681297534375946515",
        "80386287592878490201521685554828717201219257766954",
        "78182833757993103614740356856449095527097864797581",
        "16726320100436897842553539920931837441497806860984",
        "48403098129077791799088218795327364475675590848030",
        "87086987551392711854517078544161852424320693150332",
        "59959406895756536782107074926966537676326235447210",
        "69793950679652694742597709739166693763042633987085",
        "41052684708299085211399427365734116182760315001271",
        "65378607361501080857009149939512557028198746004375",
        "35829035317434717326932123578154982629742552737307",
        "94953759765105305946966067683156574377167401875275",
        "88902802571733229619176668713819931811048770190271",
        "25267680276078003013678680992525463401061632866526",
        "36270218540497705585629946580636237993140746255962",
        "24074486908231174977792365466257246923322810917141",
        "91430288197103288597806669760892938638285025333403",
        "34413065578016127815921815005561868836468420090470",
        "23053081172816430487623791969842487255036638784583",
        "11487696932154902810424020138335124462181441773470",
        "63783299490636259666498587618221225225512486764533",
        "67720186971698544312419572409913959008952310058822",
        "95548255300263520781532296796249481641953868218774",
        "76085327132285723110424803456124867697064507995236",
        "37774242535411291684276865538926205024910326572967",
        "23701913275725675285653248258265463092207058596522",
        "29798860272258331913126375147341994889534765745501",
        "18495701454879288984856827726077713721403798879715",
        "38298203783031473527721580348144513491373226651381",
        "34829543829199918180278916522431027392251122869539",
        "40957953066405232632538044100059654939159879593635",
        "29746152185502371307642255121183693803580388584903",
        "41698116222072977186158236678424689157993532961922",
        "62467957194401269043877107275048102390895523597457",
        "23189706772547915061505504953922979530901129967519",
        "86188088225875314529584099251203829009407770775672",
        "11306739708304724483816533873502340845647058077308",
        "82959174767140363198008187129011875491310547126581",
        "97623331044818386269515456334926366572897563400500",
        "42846280183517070527831839425882145521227251250327",
        "55121603546981200581762165212827652751691296897789",
        "32238195734329339946437501907836945765883352399886",
        "75506164965184775180738168837861091527357929701337",
        "62177842752192623401942399639168044983993173312731",
        "32924185707147349566916674687634660915035914677504",
        "99518671430235219628894890102423325116913619626622",
        "73267460800591547471830798392868535206946944540724",
        "76841822524674417161514036427982273348055556214818",
        "97142617910342598647204516893989422179826088076852",
        "87783646182799346313767754307809363333018982642090",
        "10848802521674670883215120185883543223812876952786",
        "71329612474782464538636993009049310363619763878039",
        "62184073572399794223406235393808339651327408011116",
        "66627891981488087797941876876144230030984490851411",
        "60661826293682836764744779239180335110989069790714",
        "85786944089552990653640447425576083659976645795096",
        "66024396409905389607120198219976047599490197230297",
        "64913982680032973156037120041377903785566085089252",
        "16730939319872750275468906903707539413042652315011",
        "94809377245048795150954100921645863754710598436791",
        "78639167021187492431995700641917969777599028300699",
        "15368713711936614952811305876380278410754449733078",
        "40789923115535562561142322423255033685442488917353",
        "44889911501440648020369068063960672322193204149535",
        "41503128880339536053299340368006977710650566631954",
        "81234880673210146739058568557934581403627822703280",
        "82616570773948327592232845941706525094512325230608",
        "22918802058777319719839450180888072429661980811197",
        "77158542502016545090413245809786882778948721859617",
        "72107838435069186155435662884062257473692284509516",
        "20849603980134001723930671666823555245252804609722",
        "53503534226472524250874054075591789781264330331690"
    };
    uint64_t sum = 0;
    for (string & s : d) sum += stoull(s.substr(0, 16));
    return stoull(to_string(sum).substr(0, 10));
}
uint64_t p14() {
    uint64_t * cache = new uint64_t[1000001];
    uint64_t best = 0, length = 0;
    for (uint64_t i = 2; i < 1000000; ++i) {
        uint64_t c, n = i;
        for (c = 0; n != 1; ++c) {
            n = ((n & 1) ? (3 * n + 1) : (n >> 1));
            if (n < 1000000) if (cache[n]) {
                c += cache[n];
                break;
            }
        }
        cache[i] = c;
        if (c > length) {
            length = c;
            best = i;
        }
    }
    return best;
}
uint64_t p15a() {
    uint64_t * n1 = new uint64_t[21], *n2 = new uint64_t[21];
    fill(n1, n1 + 21, 0);
    fill(n2, n2 + 21, 0);
    n1[0] = 1;
    for (uint64_t x = 1; x <= 20; ++x) {
        fill(n2, n2 + 21, 0);
        for (uint64_t y = 0; y < x; ++y) {
            uint64_t r {n1[y]};
            n2[y] += r, n2[y + 1] += r;
        }
        swap(n1, n2);
    }
    for (uint64_t x = 20; x >= 1; --x) {
        fill(n2, n2 + 21, 0);
        for (uint64_t y = 0; y < x; ++y) {
            n2[y] += n1[y] + n1[y + 1];
        }
        swap(n1, n2);
    }
    return n1[0];
}
uint64_t p15b() {
    double n {1}, d {1}, nn {21}, dd {1};
    for (int i {0}; i < 20; ++i) {
        n *= nn, d *= dd;
        nn += 1, dd += 1;
    }
    return static_cast<uint64_t>(n / d);
}
uint64_t p15c() {
    __m128d one {{1, 1}};
    __m128d accum {{1, 1}};
    __m128d mult {{21, 1}};
    accum = _mm_mul_pd(accum, mult);
    mult = _mm_add_pd(mult, one);
    accum = _mm_mul_pd(accum, mult);
    mult = _mm_add_pd(mult, one);
    accum = _mm_mul_pd(accum, mult);
    mult = _mm_add_pd(mult, one);
    accum = _mm_mul_pd(accum, mult);
    mult = _mm_add_pd(mult, one);
    accum = _mm_mul_pd(accum, mult);
    mult = _mm_add_pd(mult, one);
    accum = _mm_mul_pd(accum, mult);
    mult = _mm_add_pd(mult, one);
    accum = _mm_mul_pd(accum, mult);
    mult = _mm_add_pd(mult, one);
    accum = _mm_mul_pd(accum, mult);
    mult = _mm_add_pd(mult, one);
    accum = _mm_mul_pd(accum, mult);
    mult = _mm_add_pd(mult, one);
    accum = _mm_mul_pd(accum, mult);
    mult = _mm_add_pd(mult, one);
    accum = _mm_mul_pd(accum, mult);
    mult = _mm_add_pd(mult, one);
    accum = _mm_mul_pd(accum, mult);
    mult = _mm_add_pd(mult, one);
    accum = _mm_mul_pd(accum, mult);
    mult = _mm_add_pd(mult, one);
    accum = _mm_mul_pd(accum, mult);
    mult = _mm_add_pd(mult, one);
    accum = _mm_mul_pd(accum, mult);
    mult = _mm_add_pd(mult, one);
    accum = _mm_mul_pd(accum, mult);
    mult = _mm_add_pd(mult, one);
    accum = _mm_mul_pd(accum, mult);
    mult = _mm_add_pd(mult, one);
    accum = _mm_mul_pd(accum, mult);
    mult = _mm_add_pd(mult, one);
    accum = _mm_mul_pd(accum, mult);
    mult = _mm_add_pd(mult, one);
    accum = _mm_mul_pd(accum, mult);
    return static_cast<uint64_t>(accum.m128d_f64[0] / accum.m128d_f64[1]);
}
uint64_t p15d() {
    volatile unsigned arg {20};
    unsigned size {arg};
    __m128d one {{1., 1.}};
    __m128d accum {{1., 1.}};
    __m128d mult {{static_cast<double>(arg), 0.}};
    for (unsigned i {size >> 2}; i; --i) {
        mult = _mm_add_pd(mult, one);
        accum = _mm_mul_pd(accum, mult);
        mult = _mm_add_pd(mult, one);
        accum = _mm_mul_pd(accum, mult);
        mult = _mm_add_pd(mult, one);
        accum = _mm_mul_pd(accum, mult);
        mult = _mm_add_pd(mult, one);
        accum = _mm_mul_pd(accum, mult);
    }
    for (unsigned i {size & 3}; i; --i) {
        mult = _mm_add_pd(mult, one);
        accum = _mm_mul_pd(accum, mult);
    }
    return static_cast<uint64_t>(accum.m128d_f64[0] / accum.m128d_f64[1]);
}
uint64_t p15e() {
    volatile unsigned arg {20};
    unsigned size {arg};
    double n {1}, d {1}, nn {static_cast<double>(size)}, dd {0};
    for (unsigned i {size}; i; --i) {
        nn += 1, dd += 1;
        n *= nn, d *= dd;
    }
    return static_cast<uint64_t>(n / d);
}
uint64_t p16() {
    array<uint8_t, 0x200> a {{1}};
    uint8_t r;
    uint64_t x, i;
    for (x = 0; x < 1000; ++x) for (i = 0, r = 0; i < 0x200; ++i) {
        a[i] = a[i] * 2 + r;
        a[i] > 9 ? a[i] -= 10, r = 1 : r = 0;
    }
    return accumulate(a.begin(), a.end(), 0);
}
uint64_t p17() {
    return 11 + 99 * 9 * 3 + 7 * 900 + (100 + 10 * 9) * (3 + 3 + 5 + 4 + 4 + 3 + 5 + 5 + 4) + 10 * 10 * (6 + 6 + 5 + 5 + 5 + 7 + 6 + 6) + 10 * (3 + 6 + 6 + 8 + 8 + 7 + 7 + 9 + 8 + 8);
}
uint64_t p18() {
    ifstream file {"p18.txt"};
    uint64_t const size = 15;
    array<array<uint64_t, size>, size> n;
    for (auto & a : n) a.fill(0);
    for (int x = 0; x < size; ++x) for (int y = 0; y <= x; ++y) file >> n[x][y];
    array<uint64_t, size + 1> accum;
    accum.fill(0);
    for (int i = size - 1; i >= 0; --i) {
        array<uint64_t, size + 1> sum;
        sum.fill(0);
        for (int j = 0; j <= i; ++j) {
            sum[j] = max(accum[j], accum[j + 1]) + n[i][j];
        }
        copy(sum.begin(), sum.end(), accum.begin());
    }
    return accum[0];
}
uint64_t p19() {

}
uint64_t p67() {
    ifstream file {"p67.txt"};
    uint64_t const size = 100;
    array<array<uint64_t, size>, size> n;
    for (auto & a : n) a.fill(0);
    for (int x = 0; x < size; ++x) for (int y = 0; y <= x; ++y) file >> n[x][y];
    array<uint64_t, size + 1> accum, sum;
    accum.fill(0);
    sum.fill(0);
    for (int i = size - 1; i >= 0; --i) {
        for (int j = 0; j <= i; ++j) {
            sum[j] = max(accum[j], accum[j + 1]) + n[i][j];
        }
        accum.swap(sum);
    }
    return accum[0];
}
uint64_t p415() {
    //uint64_t const n = 100000000000;
    //uint64_t const s = 316228;
    //struct pair {
    //    uint64_t value;
    //    uint64_t next;
    //};
    //vector<pair> pairs;
    //pairs.push_back(pair {0, 0});
    //uint64_t * factors = reinterpret_cast<uint64_t *>(calloc(s, sizeof(uint64_t)));
    //for (uint64_t i = 2; i < s; ++i) {
    //    if (factors[i] == 0) {
    //        for (uint64_t j = i; j < s; j += i) {
    //            pairs.push_back(pair {i, factors[j]});
    //            factors[j] = pairs.size() - 1;
    //        }
    //    }
    //}
    //auto totient = [&](uint64_t p) -> uint64_t {
    //    uint64_t res = p;
    //    uint64_t top = 1;
    //    if (factors[p]) {
    //        pair next = pairs[factors[p]];
    //        for (;;) {
    //            res /= next.value;
    //            top *= next.value - 1;
    //            if (next.next == 0) break;
    //            next = pairs[next.next];
    //        }
    //    }
    //    return res * top;
    //};
    //uint64_t sum = 0;
    //for (uint64_t i = 1; i < s; ++i) {
    //    sum += totient(i);
    //}
    //return sum;
    //auto sieve(make_sieve(s));
    //auto totient = [&](uint64_t p) -> uint64_t {
    //    uint64_t res = p;
    //    uint64_t top = 1;
    //    if (!(p & 1)) {
    //        res >>= 1;
    //        while (!(p & 1)) {
    //            p >>= 1;
    //        }
    //    }
    //    uint64_t s = static_cast<uint64_t>(sqrt(p) + 1);
    //    for (uint64_t i = 3; i <= s; i += 2) if (!sieve[i]) {
    //        uint64_t d = p / i;
    //        uint64_t r = p % i;
    //        if (r == 0) {
    //            p = d;
    //            res /= i;
    //            top *= i - 1;
    //            for (;;) {
    //                uint64_t d = p / i;
    //                uint64_t r = p % i;
    //                if (r != 0) break;
    //                p = d;
    //            }
    //            if (p == 1) break;
    //            s = static_cast<uint64_t>(sqrt(p) + 1);
    //        }
    //    }
    //    if (p != 1) {
    //        res /= p;
    //        top *= p - 1;
    //    }
    //    return top * res;
    //};
    //uint64_t sum = 0;
    //for (int i = 3; i < n / 2 + 1; ++i) {
    //    sum += totient(i);
    //    if ((i & 0xfffff) == 0xfffff) {
    //        cout << i << endl;
    //    }
    //}
    //return sum;
    return 0;
}


int main2() {
    string s {s};
    //test_rep(p15a, 100000);
    test_win_rep(p15e, 10000000);
    return 0;
}
