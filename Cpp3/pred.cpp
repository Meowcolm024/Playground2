#include <algorithm>
#include <ctime>
#include <iostream>

using namespace std;

auto f(int x) -> decltype(auto)
{
    return [x](int y)
    {
        return x + y;
    };
};

class MyShow
{
public:
    virtual void myShow() = 0;
    virtual void heShow()
    {
        myShow();
        myShow();
    }
};

class yky : public MyShow
{
public:
    virtual void myShow() override
    {
        cout << "hello" << endl;
    }
};

int main()
{
    // constexpr auto arrSize = 32768u;
    // int data[arrSize];
    // for (auto c = 0; c < arrSize; c++)
    //     data[c] = rand() % 256;

    // sort(data, data + arrSize);

    // auto start = clock();
    // long sum = 0;
    // for (auto i = 0; i < 100000; i++)
    // {
    //     for (auto c = 0; c < arrSize; c++)
    //     {
    //         if (data[c] > 128)
    //             sum += data[c];
    //     }
    // }

    // auto et = static_cast<double>(clock() - start) / CLOCKS_PER_SEC;

    // cout << et << endl;

    yky hello{};
    hello.myShow();

    cout << f(1)(2) << endl;

    cout << 9 / 2 << " " << 9.0 / 2.0 << endl;
    cout << 9 / 2.0 << " " << 9.0 / 2 << endl;
    cout << boolalpha << (3 > 4) << noboolalpha << (3 < 4) << endl;

    return 0;
}
