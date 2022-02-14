#include <iostream>
#include <algorithm>
#include <vector>
#include <stack>
#include <functional>
#include <optional>

using namespace std;

struct sum
{
    stack<int> thunk;
    int acc;
    sum() : acc(0), thunk(stack<int>{}) {}
    void operator()(int i)
    {
        thunk.push(i);
    }
    int eval()
    {
        while (!thunk.empty())
        {
            acc += thunk.top();
            thunk.pop();
        }
        return acc;
    }
};

template <class T>
class lazy
{
private:
    optional<T> val;
    T (*delay)
    ();

public:
    lazy(T (*f)()) : delay(f), val(nullopt) {}
    T operator*()
    {
        if (!val)
            val = delay();
        return val.value();
    }
};

int main()
{

    auto x = vector<int>{1, 2, 3, 4, 5, 6};
    auto r = for_each(x.begin(), x.end(), sum());

    cout << r.eval() << endl;

    auto y = lazy<int>([]()
                       {
                           cout << "hello\n";
                           return 233;
                       });
    cout << *y << endl;
    cout << *y << endl;

    return 0;
}