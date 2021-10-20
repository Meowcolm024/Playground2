#include <cstring>
#include <cstdio>
#include <cinttypes>

constexpr auto n = 10;
constexpr int64_t fac(int64_t x)
{
    return x == 0 ? 1 : x * fac(x - 1);
}
constexpr auto facn = fac(n);

struct A
{
    int a;
};

struct B
{
    char a;
    char b;
    char c;
    char d;
};

class C
{
private:
    int a;

public:
    int b;

    void show() {printf("C: %d %d\n", a, b);}
};

int main()
{
    auto a = A{4};
    auto b = B{'a', 'b', 'c', 'd'};

    memcpy(&a, &b, 4);
    printf("A: %d\nB: %c%c%c%c\n", a.a, b.a, b.b, b.c, b.d);

    auto c = C();
    c.b = 10;
    *(&(c.b)-1) = 20;
    c.show();

    auto x = &C::show;
    printf("%p\n", (void*)x);

    return 0;
}