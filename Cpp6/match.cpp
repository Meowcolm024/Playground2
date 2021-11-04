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
class Maybe
{
protected:
    Maybe() = default;
    virtual ~Maybe() = default;

public:
    virtual std::vector<Just<T> *const> just() { return std::vector<Just<T> *const>(); };
    virtual std::vector<Nothing<T> *const> nothing() { return std::vector<Nothing<T> *const>(); };
};

template <class T>
class Just : public Maybe<T>
{
private:
    T value;

public:
    Just(T value) : Maybe<T>(), value(value) {}
    virtual ~Just() = default;

    T &get() { return value; }

    virtual std::vector<Just<T> *const> just() override
    {
        return std::vector<Just<T> *const>{this};
    }
};

template <class T>
class Nothing : public Maybe<T>
{
public:
    Nothing() : Maybe<T>() {}
    virtual ~Nothing() = default;

    virtual std::vector<Nothing<T> *const> nothing() override
    {
        return std::vector<Nothing<T> *const>{this};
    }
};

template <class T>
void print(Maybe<T> &y)
{
    using namespace std;
    match(i, y.just())
    {
        i->get() += 1;
        cout << i->get() << endl;
    }
    match(i, y.nothing())
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