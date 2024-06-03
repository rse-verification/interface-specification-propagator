struct Strct
{
    int f1;
};

struct Strct s;

struct Strct get_struct(){
    return s;
}

void main()
{
    struct Strct ls;
    ls = get_struct();
}