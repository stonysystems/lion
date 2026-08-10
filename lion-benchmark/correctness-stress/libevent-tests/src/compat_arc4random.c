/* glibc 2.36 added arc4random() and arc4random_buf() but deliberately did not
 * add arc4random_addrandom(), which OpenBSD had already deprecated.
 *
 * libevent 2.1.5-beta probes only for arc4random(); having found it, evutil_rand.c
 * compiles evutil_secure_rng_add_bytes() to call arc4random_addrandom(), so on
 * any glibc from 2.36 onwards every link against that release fails with an
 * undefined reference. (2.1.11 onwards probes for arc4random_addrandom
 * separately and is unaffected; older glibc supplies none of the three, so
 * libevent falls back to its own bundled implementation and is unaffected too.
 * Only the middle case breaks, which is why this went unnoticed for so long.)
 *
 * Forcing the probe off is not an option: libevent's bundled arc4random.c then
 * defines a static arc4random_buf(), which collides with glibc's declaration.
 * So the missing symbol is supplied here instead — as a weak definition linked
 * only into the test binaries, leaving the upstream archive byte-for-byte as
 * built. Anything that does provide a real arc4random_addrandom overrides this.
 *
 * The call is entropy-stirring: it folds caller-supplied bytes into the pool.
 * Under glibc the pool is kernel-seeded and re-seeded independently, so
 * discarding those bytes costs nothing these tests depend on — they measure
 * event-loop liveness, not the quality of libevent's RNG.
 */

__attribute__((weak)) void arc4random_addrandom(unsigned char *dat, int datlen);

__attribute__((weak)) void arc4random_addrandom(unsigned char *dat, int datlen)
{
	(void)dat;
	(void)datlen;
}
