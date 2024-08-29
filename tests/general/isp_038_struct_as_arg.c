/* run.config
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Testing assignment of global struct by struct argument."
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

StructB gs;

void set_global_struct(StructB a) {
    gs = a;
}

void main()
{
    StructB ls;
    set_global_struct(ls);
}
