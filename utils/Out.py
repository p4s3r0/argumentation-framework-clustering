from colorama import Fore, Back, Style

OUT_MESSAGE = f"{Style.BRIGHT + Fore.GREEN}[OUT  ]{Style.RESET_ALL} ->   "

def OUT(func):
    def wrapper(*args, **kwargs):
        print(f"{OUT_MESSAGE}", end="")
        func(*args, **kwargs)
        exit()
    return wrapper


@OUT
def Spurious(set: list) -> None:
    print(f"{Style.BRIGHT + Back.RED + Fore.BLACK} SPURIOUS! {Style.RESET_ALL} Because Set {Fore.CYAN}", end="") 
    print(set, end="")
    print(f"{Style.RESET_ALL} is spurious.")


@OUT
def Faithful() -> None:
    print(f"{Style.BRIGHT + Back.GREEN + Fore.BLACK} FAITHFUL! {Style.RESET_ALL}")


@OUT
def Admissibles(admissibles: list) -> None:
    print(f"{Style.BRIGHT}ADMISSIBLE SETS: {Style.RESET_ALL}", end="")
    for set in admissibles:
        print("{", end="")
        for arg in set:
            print(arg.name, end=",")
        print("}, ", end="")