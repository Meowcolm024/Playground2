#include <iostream>
using namespace std;

struct Droppable
{
    string name;
    Droppable(string n = "anonymous") : name(n) {}
    Droppable(const Droppable& d) {
        name = d.name;
        cout << "> Constructing via copying " << name << endl;
    }
    Droppable(Droppable &&d)
    {
        name = move(d.name);
        d.name = nullptr;
        cout << "> Constructing via moving " << name << endl;
    }
    ~Droppable() { cout << "> Dropping " << name << endl; }
    Droppable& operator=(const Droppable& d) {
        name = d.name;
        cout << "> Copying " << name << endl;
        return *this;
    }
    Droppable& operator=(Droppable&& d) {
        name = move(d.name);
        d.name = nullptr;
        cout << "> Moving " << name << endl;
        return *this;
    }
};

int main()
{
    Droppable ds[3];

    {
        auto d = Droppable("Bonjour");
        Droppable e("Hello");
        auto f = move(e);
        auto g = d;
        // ? DESTRUCTOR USE AFTER MOVE?
    }

    for (auto i = 0; i < 3; i++)
        ds[i].name = to_string(i);

    return 0;
}
