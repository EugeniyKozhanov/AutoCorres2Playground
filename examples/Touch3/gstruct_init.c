
int wrap_config_set()
{
    return 1;
}

typedef struct {
    long long aa;
    long long bb;
} test_t;


void update(test_t *p) {
  if (wrap_config_set()) 
    p->aa = 5;
  p->bb = 7;
}

void cpu_initLocalIRQController(void)
{
    test_t pext;
    update(&pext);
}
