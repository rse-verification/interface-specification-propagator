/* run.config
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Testing return of local struct."
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

StructB create_struct() {
    StructB ls;
    ls.b1.a1 = 17;
    ls.b1.a2 = 4.0f;
    ls.b2 = 23;
    return ls;
}

void main()
{
    StructB ls;
    ls = create_struct();
}