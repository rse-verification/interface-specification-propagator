/* run.config
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Testing return of global struct."
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

StructB get_struct(){
    return gs;
}

void main()
{
    StructB ls;
    ls = get_struct();
}