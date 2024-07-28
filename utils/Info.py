from colorama import Fore, Back, Style

INFO = f"{Style.BRIGHT + Fore.BLUE}[INFO ]{Style.RESET_ALL} ->   "



def info(info: str) -> None:
    print(f"{INFO}{info}")


def progress(val: str) -> None:
    print(f"{INFO}{val}", end="\r")

def progress_end() -> None:
    print()



