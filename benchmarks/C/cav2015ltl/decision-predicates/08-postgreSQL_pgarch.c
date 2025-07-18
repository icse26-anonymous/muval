//#Unsafe
// ****************************************************
//
//     Making Prophecies with Decision Predicates
//
//              Byron Cook * Eric Koskinen
//                     July 2010
//
// ****************************************************

//@ ltl invariant positive: []<>AP(wakend==1);

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume();
extern int __VERIFIER_nondet_int();

#define true 1
#define false 0
#define NULL 0
#define PGC_SIGHUP 1
#define PGARCH_AUTOWAKE_INTERVAL 1000

int last_copy_time = 0;
int curtime;
int got_SIGHUP;
int wakend;

void init() 
{
  wakend = 1; 
  got_SIGHUP = __VERIFIER_nondet_int();
}

void ProcessConfigFile(int a) 
{
	
}

int XLogArchivingActive() 
{ 
	return __VERIFIER_nondet_int(); 
}

void pgarch_ArchiverCopyLoop() 
{ 

}

int time(int a) 
{ 
	return __VERIFIER_nondet_int(); 
}

void pg_usleep(int a) 
{
	
}

int PostmasterIsAlive(int a) 
{ 
	return __VERIFIER_nondet_int(); 
}

void main() {
	init();
	/*
	 * We run the copy loop immediately upon entry, in case there are
	 * unarchived files left over from a previous database run (or maybe
	 * the archiver died unexpectedly).  After that we wait for a signal
	 * or timeout before doing more.
	 */
	wakend = true;

	do
	{
		/* Check for config update */
		if (got_SIGHUP)
		{
			got_SIGHUP = false;
			ProcessConfigFile(PGC_SIGHUP);
			if (!XLogArchivingActive())
				break;                  /* user wants us to shut down */
		}
		/* Do what we're here for */
		if (wakend)
		{
			wakend = false;
			pgarch_ArchiverCopyLoop();
			last_copy_time = time(NULL);
		}
		/*
		 * There shouldn't be anything for the archiver to do except to
		 * wait for a signal, ... however, the archiver exists to
		 * protect our data, so she wakes up occasionally to allow
		 * herself to be proactive. In particular this avoids getting
		 * stuck if a signal arrives just before we sleep.
		 */
		if (!wakend)
		{
			pg_usleep(PGARCH_AUTOWAKE_INTERVAL * 1000000L);

			curtime = time(NULL);
			if ((unsigned int) (curtime - last_copy_time) >= (unsigned int) PGARCH_AUTOWAKE_INTERVAL)
			{
				wakend = true;
			}
		}
	} while (PostmasterIsAlive(true));

	while(1) { int ddd; ddd=ddd;}
}
