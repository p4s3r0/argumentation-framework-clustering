from colorama import Fore, Back, Style

INFO = f"{Style.BRIGHT + Fore.BLUE}[INFO ]{Style.RESET_ALL} ->   "

DEBUG = True


def info(info: str) -> None:
    if not DEBUG: return
    print(f"{INFO}{info}")


def progress(val: str) -> None:
    if not DEBUG: return
    print(f"{INFO}{val}", end="\r")

def progress_end() -> None:
    if not DEBUG: return
    print()



