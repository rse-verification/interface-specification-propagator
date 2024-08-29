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
} StructB;

StructB gs;

/*@
  ensures -313 <= \result.b1.a1 <= 17;
  ensures -10.0<= \result.b1.a2 <= 10.0;
  ensures -2989 <= \result.b2 <= 49374;
  assigns \result \from \nothing;
*/
StructB get_struct(void);

void set_global_struct(StructB a) {
    gs = a;
}

void main()
{
    StructB ls = get_struct();
    set_global_struct(ls);
}
