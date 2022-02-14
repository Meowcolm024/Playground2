#include <iostream>
using namespace std;

struct What
{
    unsigned int id;
    What *next;
    What *infectee;
};

void traverse(const What *x, int align)
{
    if (!x)
        return;
    for (int i = 0; i < align; i++)
        cout << "\t";
    cout << x->id << "\n";
    traverse(x->infectee, align + 1);
    traverse(x->next, align);
}

int main()
{
    // int *a = new int(10);
    What e = {4, nullptr, nullptr};
    What a = {3, nullptr, nullptr};
    What b = {2, &a, nullptr};
    What c = {1, nullptr, &e};
    What d = {0, &b, &c};
    traverse(&d, 0);
    return 0;
}
