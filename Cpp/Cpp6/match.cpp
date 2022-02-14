#include <iostream>
#include <vector>

#define match(v, x) for (auto &v : x)

template <class T>
class Maybe;

template <class T>
class Just;

template <class T>
class Nothing;

template <class T>
struct Maybe
{
protected:
    Maybe() = default;
    virtual ~Maybe() = default;

public:
    virtual std::vector<Just<T> *const> just() noexcept { return std::vector<Just<T> *const>(); };
    virtual std::vector<Nothing<T> *const> nothing() noexcept { return std::vector<Nothing<T> *const>(); };
};

template <class T>
struct Just final : public Maybe<T>
{
    T value;

    Just(T value) : Maybe<T>(), value(value) {}

    virtual std::vector<Just<T> *const> just() noexcept override
    {
        return std::vector<Just<T> *const>{this};
    }
};

template <class T>
struct Nothing final : public Maybe<T>
{
    Nothing() : Maybe<T>() {}

    virtual std::vector<Nothing<T> *const> nothing() noexcept override
    {
        return std::vector<Nothing<T> *const>{this};
    }
};

template <class T>
void print(Maybe<T> &y)
{
    using namespace std;
    for (auto &i : y.just())
    {
        i->value += 1;
        cout << i->value << endl;
    }
    for (auto &i : y.nothing())
    {
        cout << "haha" << endl;
    }
}

int main()
{
    auto x = Just<int>(2);
    auto y = Nothing<char>();

    print(x);
    print(y);

    return 0;
}