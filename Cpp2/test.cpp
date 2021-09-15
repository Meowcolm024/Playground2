#include <cstdio>
#include <iostream>
#include <vector>
using namespace std;

constexpr int sqrsum(int a, int b) noexcept
{
    return a * a + b * b;
}

constexpr auto x = 4;
constexpr auto gg = sqrsum(3, x);

constexpr unsigned long fact(unsigned long a)
{
    return (a == 0) ? 1 : a * fact(a - 1);
}

constexpr auto fact5 = fact(15);

auto hello(int a, int b) -> decltype(auto)
{
    cout << "hello" << endl;
    int x = a + b;
    return x * 2;
}

template <typename Container, typename Index>
auto access(Container &&c, Index i) -> decltype(std::forward<Container>(c)[i])
{
    cout << "Done it!" << endl;
    return std::forward<Container>(c)[i];
}

class Base
{
private:
    /* data */
public:
    Base() {}
    // ~Base();
    virtual void greet()
    {
        cout << "Hello from Base" << endl;
    }
};

class Derived : public Base
{
private:
    /* data */
public:
    Derived() : Base() {}
    // ~Derived();
    virtual void greet() override
    {
        cout << "Hello from Derived" << endl;
    }
};

class Box
{
private:
    string secret;

public:
    Box() : secret("secret!") {}
    ~Box() {}

    string &GetSecret() &
    {
        return secret;
    }

    string GetSecret() &&
    {
        return move(secret);
    }
};

auto newBox() -> Box
{
    return Box();
}

int main()
{
    int i = 10;
    int &j = i;
    const int &k = i;

    i += 5;
    j = 5;

    printf("%d %d %d\n", i, j, k);
    int a_ = hello(1, 2);

    vector<bool> cats{true, false, false, true, true};
    auto a = cats[1];
    cout << a << endl;

    Base b = Base();
    Derived d = Derived();

    b.greet();
    d.greet();
    static_cast<Base *>(&d)->greet();

    auto ba = newBox().GetSecret();
    auto bb = newBox();
    auto bc = bb.GetSecret();

    cout << ba << " " << bc << endl;

    cout << fact(10) << endl;

    return 0;
}