from typing import List
from slither.core.cfg.node import Node
from slither.core.declarations.solidity_variables import SolidityVariable
from slither.slithir.operations import HighLevelCall, LibraryCall, Operation
from slither.core.declarations import Contract, Function, SolidityVariableComposed
from slither.analyses.data_dependency.data_dependency import is_dependent
from slither.core.compilation_unit import SlitherCompilationUnit
import winsound


def check_only(f):
    for mod in f.modifiers:
        #if mod.name[0:4] == "only":
        if "only" in mod.name or "auth" in mod.name:
            print(f"很遗憾, 好像被only了: ,{f.full_name} {mod.name}")
            return True
    return False

def check_from_addr_in_statevars(ir: HighLevelCall, node: Node):
    arg0typeStr = str(type(ir.arguments[0]))
    if 'StateVariable' in arg0typeStr:
        print(f"蛮遗憾, transferFrom的victim好像来自状态变量(calldata无法指定), {ir.arguments[0].name} 的type:{arg0typeStr}")
        return True
    else:
        try:
            all_statevars_names = [item.name for item in node.function.contract.all_state_variables_read]
            arg0type2 = str(type(node.expression.arguments[0]))
            if 'Identifier' in arg0type2 and node.expression.arguments[0].value.name in all_statevars_names:
                print(f"蛮遗憾, [Identifier]{node.expression.arguments[0].value.name} transferFrom的victim好像来自状态变量(calldata无法指定), arg0type2:{arg0type2}")
                return True
            elif 'TypeConversion' in arg0type2 and 'StateVariable' in str(type(node.expression.arguments[0].expression.value)):
                print(f"蛮遗憾, [TypeConversion]{node.expression.arguments[0].expression.value.name}  transferFrom的victim好像来自状态变量(calldata无法指定), arg0type2:{arg0type2}")
                return True
        except Exception as e:
            print(f"解析node.expression.arguments异常了: {str(e)}")
        return False

def check_function_signture_too_simple(node: Node): # 如果参数过于简单，calldata也没法构造受害者地址
    purelist = ['int','uint','uint256','uint128','uint64','uint32','uint16','uint8','bool']
    for _param_type in node.function.signature[1]:
        if _param_type not in purelist:
            return False
    print(f"挺遗憾, 参数类型太单纯: {node.function.signature_str}")
    return True


def check_parent_outed(funcs):
    for ff in funcs:
        if not check_only(ff) and (ff.visibility == "public" or ff.visibility == "external"):
            return True
    return False

class ArbitrarySendErc20:
    """Detects instances where ERC20 can be sent from an arbitrary from address."""

    def __init__(self, compilation_unit: SlitherCompilationUnit):
        self._compilation_unit = compilation_unit
        self._no_permit_results: List[Node] = []
        self._permit_results: List[Node] = []

    @property
    def compilation_unit(self) -> SlitherCompilationUnit:
        return self._compilation_unit

    @property
    def no_permit_results(self) -> List[Node]:
        return self._no_permit_results

    @property
    def permit_results(self) -> List[Node]:
        return self._permit_results

    def _detect_arbitrary_from(self, contract: Contract):
        for f in contract.functions:
            all_high_level_calls = [
                f_called[1].solidity_signature
                for f_called in f.high_level_calls
                if isinstance(f_called[1], Function)
            ]
            all_library_calls = [f_called[1].solidity_signature for f_called in f.library_calls]
            if (
                "transferFrom(address,address,uint256)" in all_high_level_calls
                or "safeTransferFrom(address,address,address,uint256)" in all_library_calls
            ):
                if (
                    "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)"
                    in all_high_level_calls
                ):
                    ArbitrarySendErc20._arbitrary_from(f.nodes, self._permit_results)
                else:
                    ArbitrarySendErc20._arbitrary_from(f.nodes, self._no_permit_results)



    @staticmethod
    def _arbitrary_from(nodes: List[Node], results: List[Node]):
        """Finds instances of (safe)transferFrom that do not use msg.sender or address(this) as from parameter."""
        for node in nodes:
            if check_only(node.function):
                return
            for ir in node.irs:
                check_father = False
                if (
                    isinstance(ir, HighLevelCall)
                    and isinstance(ir.function, Function)
                    and ir.function.solidity_signature == "transferFrom(address,address,uint256)"
                    and not (
                        is_dependent(
                            ir.arguments[0],
                            SolidityVariableComposed("msg.sender"),
                            node.function.contract,
                        )
                        or is_dependent(
                            ir.arguments[0],
                            SolidityVariable("this"),
                            node.function.contract,
                        )
                    )
                ):
                    check_father = True
                elif (
                    isinstance(ir, LibraryCall)
                    and ir.function.solidity_signature
                    == "safeTransferFrom(address,address,address,uint256)"
                    and not (
                        is_dependent(
                            ir.arguments[1],
                            SolidityVariableComposed("msg.sender"),
                            node.function.contract,
                        )
                        or is_dependent(
                            ir.arguments[1],
                            SolidityVariable("this"),
                            node.function.contract,
                        )
                    )
                ):
                    check_father = True
                check_victim_in_statevar = False
                if check_father:
                    if node.function.visibility == "public" or node.function.visibility == "external":
                        # results.append(ir.node)
                        # winsound.Beep(200,800)
                        check_victim_in_statevar = True
                    else:
                        funcs = node.function.reachable_from_functions
                        for xx in range(3):
                            if check_parent_outed(funcs):
                                # results.append(ir.node)
                                # winsound.Beep(200,800)
                                check_victim_in_statevar = True
                                break
                            else:
                                temp =[]
                                for ff in funcs:
                                    temp += ff.reachable_from_functions
                                funcs = temp

                if check_victim_in_statevar: # 说明check_father上一步都通过
                    if not check_from_addr_in_statevars(ir,node):
                        #不在状态变量才能被calldata指定
                        if not check_function_signture_too_simple(node):
                            #参数类型不能太单纯
                            results.append(ir.node)
                            winsound.Beep(300,1000)




    def detect(self):
        """Detect transfers that use arbitrary `from` parameter."""
        for c in self.compilation_unit.contracts_derived:
            self._detect_arbitrary_from(c)
