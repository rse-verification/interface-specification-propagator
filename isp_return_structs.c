struct StructA
{
    int f3;
    float f4;
};

struct StructB
{
    struct StructA f1;
    int f2;
};

struct StructB gs;

struct StructB create_struct() {
    struct StructB ls;
    ls.f1.f4 = 4.0f;
    ls.f1.f3 = 3;
    ls.f2 = 2;
    return ls;
}

/*
struct StructB get_struct(){
    gs.f1.f4 = 1.0f;
    gs.f1.f3 = 2;
    gs.f2 = 1;
    return gs;
}

void init_struct(struct StructB *s){
    s->f1.f4 = 1.0f;
    s->f1.f3 = 2;
    s->f2 = 1;
}

void set_struct(struct StructB a) {
    gs = a;
}
*/

void main()
{
    struct StructB ls;
    ls = create_struct();
//    set_struct(ls);
//    ls = get_struct();
}
