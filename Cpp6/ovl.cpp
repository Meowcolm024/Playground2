#include <iostream>
using namespace std;

struct Vec
{
    double x;
    double y;

    Vec(double x = 0, double y = 0) : x(x), y(y) {}

    // * higher priority
    // * DONOT define both
    Vec operator+(const Vec &p)
    {
        return Vec(x + p.x, y + p.y);
    }

    double operator[](size_t i) const
    {
        switch (i)
        {
        case 0:
            return x;
        case 1:
            return y;
        default:
            // the bottom type
            throw runtime_error("ERROR!");
        }
    }

    friend double operator*(const Vec &p, const Vec &q) noexcept
    {
        return p.x * q.x + p.y * q.y;
    }

    friend ostream &operator<<(ostream &os, Vec &v)
    {
        os << "Vec(" << v.x << ", " << v.y << ").";
        return os;
    }
};

string to_string(const Vec &v)
{
    return "Vec(" + to_string(v.x) + ", " + to_string(v.y) + ").";
}

int main()
{
    auto v1 = Vec(3, 4);
    auto v2 = v1 + 2.5;
    auto v3 = (Vec)6.7 + v1;

    cout << v1 << endl
         << v2 << endl;
    cout << v3[0] << endl
         << v1 * v2 << endl;

    auto a = 10;
    auto b = 3;
    // assoc right
    auto c = a += b += a += b += a;

    cout << a << " " << b << " " << endl;;

    return 0;
}