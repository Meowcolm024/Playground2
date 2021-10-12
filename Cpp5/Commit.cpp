#include <iostream>

struct Commit
{
    int index;
    Commit *parent;
    Commit *second_parent;
    Commit(int i, Commit *p = nullptr, Commit *sp = nullptr) : index(i), parent(p), second_parent(sp) {}
};

struct Node
{
    Commit *commit;
    Node *next;
    bool marked;
    int origin;
    Node(Commit *c, Node *n = nullptr, int o = 0) : commit(c), next(n), marked(false), origin(o) {}
    ~Node()
    {
        if (next)
            delete next;
    }
};

struct Set
{
    Node *nodes;
    Set() : nodes(nullptr) {}
    ~Set()
    {
        if (nodes)
            delete nodes;
    }

    // check element existance
    const Node *exist(const Commit *commit) const
    {
        for (Node *n = nodes; n != nullptr; n = n->next)
        {
            if (n->commit == commit)
                return n;
        }
        return nullptr;
    }

    // push element to set, return true on success
    const Node *push(Commit *commit, int origin)
    {
        if (!commit)
            return nullptr;
        auto *tmp = exist(commit);
        if (tmp)
        {
            return tmp;
        }
        else
        {
            Node *n = new Node(commit, nodes, origin);
            nodes = n;
            return n;
        }
    }

    // traverse unmarked element
    Commit *expand()
    {
        if (!nodes)
            return nullptr;
        for (Node *n = nodes; n != nullptr; n = n->next)
        {
            if (n->marked)
                break;
            n->marked = true;
            const Node* x = push(n->commit->parent, n->origin);
            const Node* y = push(n->commit->second_parent, n->origin);
            if (x && x->origin != n->origin)
                return n->commit->parent;
            else if (y && y->origin != n->origin)
                return n->commit->second_parent;
        }
        return expand();
    }
};

Commit *get_lca(Commit *c1, Commit *c2)
{
    if (c1 == c2)
        return c1;

    Set s = Set();
    s.push(c1, 1);
    s.push(c2, 2);
    Commit *common = s.expand();

    return common;
}

int main()
{
    using std::cout;
    using std::endl;

    //       / 2 - 3  - 4  \ _  
    // I - 1 - 5 - 6  - 7  - 8  - ?
    //       \ 9 - 10 - 11 - 12 /
    auto init = Commit(0);
    auto c1 = Commit(1, &init);
    auto c2 = Commit(2, &c1);
    auto c5 = Commit(5, &c1);
    auto c6 = Commit(6, &c5);
    auto c3 = Commit(3, &c2, &c5);
    auto c4 = Commit(4, &c3);
    auto c7 = Commit(7, &c6);
    auto c8 = Commit(8, &c7, &c4);
    auto c9 = Commit(9, &c1);
    auto c10 = Commit(10, &c9);
    auto c11 = Commit(11, &c10, &c6);
    auto c12 = Commit(12, &c11);
   
    auto common = get_lca(&c1, &c9);

    if (common)
        cout << common->index << endl;
    else
        cout << "Not found" << endl;

    return 0;
}