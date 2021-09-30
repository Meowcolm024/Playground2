#include <iostream>
// #include <memory>
using namespace std;

struct Point {
    int x;
    int y;
};

string to_string(const Point& p) {
    return "Point(" + to_string(p.x) + "," + to_string(p.y) + ")";
}

template<typename T>
string fmt(string s, T v) {
    int i = 0;
    for (; i < s.length()-1; i++)
        if (s[i] == '{' && s[i+1] =='}')
            break;
    if (s[i] == '{')
        return s.substr(0, i) + to_string(v) + s.substr(i+2, s.length());
    else
        return "";
} 

int main() {
    string a = "hello";
    string b = " world";
    cout << a + b << endl;

    string x= to_string(100);
    cout << x << endl;

    auto p = Point{3, 4};

    cout << to_string(Point{12,16}) << endl;

    cout << fmt("hello {} world", p) << endl;

    return 0; 
}
