using System.Linq;

namespace FolThresholdParser.BapaFormula
{
    public abstract class BapaSetExpression
    {
        public abstract string ToOcamlBapa();
    }


    public class BapaSetVar : BapaSetExpression
    {
        private readonly string _varName;

        public BapaSetVar(string varName)
        {
            _varName = varName;
        }

        public override string ToOcamlBapa()
        {
            return $"Setvar \"{_varName}\"";
        }
    }


    public class BapaSetOperation : BapaSetExpression
    {
        private readonly NatRelation _operation;
        private readonly BapaSetExpression[] _expressions;

        public enum NatRelation
        {
            Union, Intersection,
        }

        public BapaSetOperation(NatRelation operation, BapaSetExpression[] expressions)
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
