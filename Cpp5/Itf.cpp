#include <iostream>
using namespace std;

// Interface
class IString
{
public:
    virtual string toString() const = 0;
    virtual ~IString() = default;
};

class Point : public IString
{
private:
    int x;
    int y;

public:
    Point(int a, int b) : x(a), y(b) {}

    virtual string toString() const override
    {
        return "Point(" + to_string(x) + "," + to_string(y) + ")";
    }
};

class Mat : public IString
{
private:
    int m[2][2];

public:
    Mat(int a, int b, int c, int d)
    {
        m[0][0] = a;
        m[0][1] = b;
        m[1][0] = c;
        m[1][1] = d;
    }

    virtual string toString() const override
    {
        return "Mat[[" + to_string(m[0][0]) + "," + to_string(m[0][1]) + "],[" + to_string(m[1][0]) + "," + to_string(m[1][1]) + "]]";
    }
};

void printing(const IString *const x)
{
    cout << x->toString() << endl;
}

int main()
{
    auto x = Point(12, 34);
    auto y = Mat(1, 2, 3, 4);
    printing(&x);
    printing(&y);
    return 0;
}