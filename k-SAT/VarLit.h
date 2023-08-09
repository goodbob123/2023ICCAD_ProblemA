#ifndef VARLIT_H
#define VARLIT_H

typedef int Var;

class Lit {
    int x;
public:
    Lit() : x(0) {}
    ~Lit() {}
    explicit Lit(Var var, bool sgn = false) : x(sgn ? -var : var) {}
    friend Lit operator ~ (Lit p);
    friend int toInt(Lit p);
};

inline Lit operator ~ (Lit p) { Lit q; q.x = -p.x; return q; }
inline int toInt(Lit p) { return p.x;}

#endif // VARLIT_H