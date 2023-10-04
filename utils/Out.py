from colorama import Fore, Back, Style

OUT_MESSAGE = f"{Style.BRIGHT + Fore.GREEN}[OUT  ]{Style.RESET_ALL} ->   "

def OUT(func):
    def wrapper(*args, **kwargs):
        print(f"{OUT_MESSAGE}", end="")
        func(*args, **kwargs)
        exit()
    return wrapper


@OUT
def Spurious(set: list()) -> None:
    print(f"{Style.BRIGHT + Back.RED} SPURIOUS! {Style.RESET_ALL} Because Set {Fore.CYAN + set + Style.RESET_ALL} is spurious.")

@OUT
def Faithful() -> None:
    print(f"{Style.BRIGHT + Back.GREEN} FAITHFUL! {Style.RESET_ALL}")
