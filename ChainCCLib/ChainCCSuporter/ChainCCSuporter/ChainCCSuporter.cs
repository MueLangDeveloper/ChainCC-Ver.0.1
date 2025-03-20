namespace ChainCCSuporter
{
    public class LockedCode
    {
        public string First { get; set; } = "";
        public string Last { get; set; } = "";
    }
    public struct Dynamic(dynamic _d)
    {
        public dynamic Value { get; set; } = _d;
    }
    public enum StackOption
    {
        ShowStack = 0,
        HideStack = 1,
    }
    public readonly struct LabelInfo(string _name)
    {
        public string Name { get; init; } = _name;
    }
    public struct DynamicStack()
    {
        private Stack<dynamic> _stack = new();
        public static implicit operator DynamicStack(Stack<dynamic> stack) => new()
        {
            _stack = stack,
        };
        public readonly void Push(dynamic d) => _stack.Push(d);
        public readonly dynamic Pop() => _stack.Pop();
        public readonly Stack<dynamic> Stack => _stack;
        public readonly int Count => _stack.Count;
    }
    public class ChainCCEval
    {
        public static dynamic Eval(string ope, dynamic v1, dynamic v2) => ope switch
        {
            "add" => v1 + v2,
            "sub" => v1 - v2,
            "mul" => v1 * v2,
            "div" => v1 / v2,
            "rem" => v1 % v2,
            "pow" => Math.Pow(v1, v2),
            "ceq" => v1 == v2,
            "cneq" => v1 != v2,
            "clt" => v1 < v2,
            "cgt" => v1 > v2,
            "ceqlt" => v1 <= v2,
            "ceqgt" => v1 >= v2,
            "and" => v1 && v2,
            "or" => v1 || v2,
            _ => throw new NotImplementedException()
        };
    }
}
