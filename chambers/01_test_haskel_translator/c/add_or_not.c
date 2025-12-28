/* Modern seL4-style configuration variable
 * By making this extern, it becomes a symbolic value that verification
 * can reason about - we prove correctness for ANY value of this variable.
 */
extern int CONFIG_WRAP_SET;

/* Function is correct for BOTH CONFIG_WRAP_SET=0 AND CONFIG_WRAP_SET=1
 * The modern seL4 approach proves both cases simultaneously using case analysis
 */
int add_or_not(int a, int b) {
    /* Conditional branch based on configuration
     * AutoCorres will preserve both branches, allowing us to prove both cases
     */
    if (CONFIG_WRAP_SET)
        return a - b;
    else
        return a + b - 3;
}
