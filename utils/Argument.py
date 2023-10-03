import z3


class Argument:
    def __init__(self, name: str) -> None:
        self.name = name
        self.attacks = list()
        self.defends = list()
        self.z3_value = z3.Bool(f'{name}')
        self.is_singleton = True
        self.clustered_arguments = list()

    def __repr__(self) -> str:
        return f"ARG: {self.name}"