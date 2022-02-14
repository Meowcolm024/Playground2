#include <iostream>
#include <memory>
using namespace std;

void **makeBox(string &&s, int &&i)
{
    void **box = (void **)(new int[2]());
    string *sa = new string(s);
    int *ia = new int(i);
    box[0] = (void *)sa;
    box[1] = (void *)ia;
    return box;
}

string &getName(void **box)
{
    return *(string *)box[0];
}

int &getAge(void **box)
{
    return *(int *)box[1];
}

void dropBox(void **box)
{
    delete (string *)box[0];
    delete (int *)box[1];
    delete box;
    box = nullptr;
}

int main()
{
    auto hi = make_unique<int>(233);
    auto ha = new int(233);

    auto ho = move(hi);
    auto he = ha;

    int arr[] = {1, 2, 3};
    1 [arr] = 8;
    for (auto i : arr)
        cout << i << endl;

    delete ha;

    void *box[2];
    string omg = "omg";
    int bbb = 34;
    box[0] = (void *)(&omg);
    box[1] = (void *)(&bbb);
    cout << *(string *)(box[0]) << " " << *(int *)(box[1]) << endl;

    auto b = makeBox("Ben", 20);
    getAge(b) += 1;
    cout << getName(b) << " " << getAge(b) << endl;
    dropBox(b);

    return 0;
}
