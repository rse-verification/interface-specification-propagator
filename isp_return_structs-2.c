typedef struct
{
    int a1;
    float a2;
} StructA;

typedef struct
{
    StructA b1;
    int b2;
} StructB ;

StructB gs;

StructB create_struct() {
    StructB ls;
    ls.b1.a1 = 17;
    ls.b1.a2 = 4.0f;
    ls.b2 = 23;
    return ls;
}

StructB get_struct(){
    gs.b1.a1 = 2;
    gs.b1.a2 = 1.0f;
    gs.b2 = 1;
    return gs;
}

void init_struct(StructB *s){
    s->b1.a1 = 84;
    s->b1.a2 = 2.7f;
    s->b2 = 42;
}

void set_struct(StructB a) {
    gs = a;
}

void main()
{
    StructB ls;
    ls = create_struct();
    init_struct(&ls);
    set_struct(ls);
    ls = get_struct();
}