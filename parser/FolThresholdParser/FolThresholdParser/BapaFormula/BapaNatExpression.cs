using System.Linq;

namespace FolThresholdParser.BapaFormula
{
    public abstract class BapaNatExpression
    {
        public abstract string ToOcamlBapa();
    }

    public class BapaNatVar : BapaNatExpression
    {
        private readonly string _varName;

        public BapaNatVar(string varName)
        {
            _varName = varName;
        }

        public override string ToOcamlBapa()
        {
            return $"Intvar \"{_varName}\"";
        }
    }

    public class BapaNatConst : BapaNatExpression
    {
        private readonly int _constant;

        public BapaNatConst(int constant)
        {
            _constant = constant;
        }

        public override string ToOcamlBapa()
        {
            return $"Const {_constant}";
        }
    }

    public class BapaCard : BapaNatExpression
    {
        private readonly BapaSetExpression _expr;

        public BapaCard(BapaSetExpression expr)
        {
            _expr = expr;
        }

        public override string ToOcamlBapa()
        {
            return $"Card ({_expr.ToOcamlBapa()})";
        }
    }

    public class BapaNatOperation : BapaNatExpression
    {
        private readonly NatRelation _operation;
        private readonly BapaNatExpression _expr1;
        private readonly BapaNatExpression _expr2;

        public enum NatRelation
        {
            Plus, Minus
        }

        public BapaNatOperation(NatRelation operation, BapaNatExpression expr1, BapaNatExpression expr2)
        {
            _operation = operation;
            _expr1 = expr1;
            _expr2 = expr2;
        }

        public override string ToOcamlBapa()
        {
            return $"{_operation} [{_expr1.ToOcamlBapa()}; {_expr2.ToOcamlBapa()}]";
        }
    }

    public class BapaNatConstantMul : BapaNatExpression
    {
        private readonly int _constant;
        private readonly BapaNatExpression _expr;

        public enum NatRelation
        {
            Plus,
        }

        public BapaNatConstantMul(int constant, BapaNatExpression expr)
        {
            _constant = constant;
            _expr = expr;
        }

        public override string ToOcamlBapa()
        {
            return
                $"{BapaNatOperation.NatRelation.Plus} [{string.Join("; ", Enumerable.Repeat(_expr.ToOcamlBapa(), _constant).ToArray())}]";
        }
    }
}
