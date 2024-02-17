from colorama import Fore, Back, Style

OUT_MESSAGE = f"{Style.BRIGHT + Fore.GREEN}[OUT  ]{Style.RESET_ALL} ->   "

def OUT(func):
    def wrapper(*args, **kwargs):
        #print(f"{OUT_MESSAGE}", end="")
        func(*args, **kwargs)
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
def SolutionSets(semantic: str, sets: list, name: str = "") -> None:

    semantic_text = ""
    if semantic == "AD":
        semantic_text = "ADMISSIBLE"
    elif semantic == "CF":
        semantic_text = "CONFLICT-FREE"
    else:
        semantic_text = "STABLE"
    print(f"{Style.BRIGHT}{semantic_text} SETS: {Style.RESET_ALL} {name}", end="")
    for set in sets:
        print("{", end="")
        for arg in set:
            print(arg.name, end=",")
        print("}, ", end="")
    print("")


@OUT
def CurrSolution(amount: int) -> None:
    print(f"Current Solutions Found {Fore.CYAN + Style.BRIGHT}{amount}{Style.RESET_ALL}", end="\r")