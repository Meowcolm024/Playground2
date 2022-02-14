#include <iostream>
#include <cstring>

using namespace std;

struct Name {
    char first[12];
    char last[12];
};

void makeName(Name &name, const char* f, const char* l) {
    strcpy(name.first, f);
    strcpy(name.last, l);
}

int main() {

    Name n;
    makeName(n, "hahahahahahahahahahaha", "byebyebyebyebye");

    cout << n.first << "\n" << n.last << endl;

    return 0;
}