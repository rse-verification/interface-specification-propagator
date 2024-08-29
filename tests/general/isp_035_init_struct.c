/* run.config
OPT: -autoload-plugins -isp -isp-print
COMMENT: "Testing initialization of structs through pointer."
*/

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

void init_struct(StructB *s){
    s->b1.a1 = 84;
    s->b1.a2 = 2.7f;
    s->b2 = 42;
}

void main()
{
    StructB ls;
    init_struct(&ls);
}