#include <iostream>
#include <cstdio>
#include <memory>

using namespace std;

int &fa(int &a) { return a; }

int &&fb(int &a) { return static_cast<int &&>(a); }

auto delInt = [](int *pI)
{
    cout << "deleted " << *pI << endl;
    delete pI;
};

struct counter
{
    int *count;

    counter()
    {
        count = new int(1);
    }

    counter(const counter &c)
    {
        count = c.count;
        (*count)++;
    }

    counter(counter &&c)
    {
        count = c.count;
        c.count = nullptr;
    }

    ~counter()
    {
        if (count != nullptr)
        {
            (*count)--;
            cout << "remaining counter: " << *count << endl;
            if (*count == 0)
                delete count;
        }
    }

    counter &operator=(const counter &c)
    {
        if (count != nullptr)
        {
            (*count)--;
            if (count == 0)
                delete count;
        }
        count = c.count;
        (*count)++;
        return *this;
    }

    counter &operator=(counter &&c)
    {
        if (count != nullptr)
        {
            (*count)--;
            if (count == 0)
                delete count;
        }
        count = c.count;
        c.count = nullptr;
        return *this;
    }

    void show() const
    {
        cout << "count: " << *count << endl;
    }
};

int main()
{
    int a = 10;
    fa(a) = 2;
    cout << a << endl;
    unique_ptr<int, decltype(delInt)> x(new int(10), delInt);

    auto p = counter();
    auto z = counter();
    p.show();
    {
        auto r = p;
        auto q = p;
        auto d = move(r);
        q.show();
    }
    {
        auto x = z;
    }
    p.show();

    return 0;
}