#include <iostream>
using namespace std;

struct Box
{
    int value = 0;
    Box() = default;
    Box(int n) : value(n) {}

    const int &getValue() const &
    {
        cout << "get from lvaule ref" << endl;
        return value;
    }

    int &&getValue() &&
    {
        cout << "get from rvalue ref" << endl;
        return move(value);
    }
};

int main()
{
    auto b = Box();
    
    auto a = Box().getValue();
    auto d = b.getValue();
    auto c = move(b).getValue();

    return 0;
}