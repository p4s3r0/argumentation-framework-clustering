from colorama import Fore, Back, Style

SPECS_MESSAGE = f"{Fore.LIGHTBLACK_EX}[SPECS]   "

DEBUG = True



def SPECS(func):
    def wrapper(*args, **kwargs):
        if not DEBUG: return
        print(f"{SPECS_MESSAGE}", end="")
        func(*args, **kwargs)
    return wrapper



@SPECS
def printCPUTime(time: float) -> None:
    if not DEBUG: return;
    print(f"CPU-Time:    {time:.3f} s{Style.RESET_ALL}")

@SPECS
def printRuntime(time: float) -> None:
    if not DEBUG: return;
    print(f"Runtime:     {time:.3f} s{Style.RESET_ALL}")


@SPECS
def printMemoryUsage(memory: float) -> None:
    if not DEBUG: return;
    print(f"Memory RSS:  {memory:.5f} MB{Style.RESET_ALL}")