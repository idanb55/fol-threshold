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
        private readonly BapaNatExpression[] _expressions;

        public enum NatRelation
        {
            Plus,
        }

        public BapaNatOperation(NatRelation operation, BapaNatExpression[] expressions)
        {
            _operation = operation;
            _expressions = expressions;
        }

        public override string ToOcamlBapa()
        {
            return $"{_operation} [{string.Join("; ", _expressions.Select(expr => expr.ToOcamlBapa()).ToArray())}]";
        }
    }
}
