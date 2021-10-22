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

bool isParent(const Commit *p, const Commit *c) {
    if (!p)
        return false;
    else {
        if (!c)
            return false;
        else if (p == c)
            return true;
        else
            return isParent(p, c->parent) || isParent(p, c->second_parent);
    }
}

Commit *get_lca(Commit *c1, Commit *c2)
{
    if (c1 == c2)
        return c1;
    
    if (isParent(c1, c2))
        return c1;
    else if (isParent(c2, c1))
        return c2;

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

    auto init = Commit(0);
    auto c1 = Commit(1, &init);
    auto c3 = Commit(3, &c1);
    auto c2 = Commit(2, &c1, &c3);
    auto c4 = Commit(4, &c2);
    auto c6 = Commit(6, &c3, &c4);
    auto c5 = Commit(5, &c6);
   
    auto common = get_lca(&c2, &c5);

    if (common)
        cout << common->index << endl;
    else
        cout << "Not found" << endl;

    return 0;
}