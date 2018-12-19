using System.Linq;

namespace FolThresholdParser.BapaFormula
{
    public abstract class BapaFormula
    {
        public abstract string ToOcamlBapa();
    }

    public class BapaBind : BapaFormula
    {
        private readonly BapaBindType _type;
        private readonly string _varName;
        private readonly BapaFormula _inner;

        public enum BapaBindType
        {
            Forallnat,
            Existsnat,
            Forallset,
            Existsset
        }

        public BapaBind(BapaBindType type, string varName, BapaFormula inner)
        {
            _type = type;
            _varName = varName;
            _inner = inner;
        }

        public override string ToOcamlBapa()
        {
            return $"Bind({_type}, \"{_varName}\", {_inner.ToOcamlBapa()})";
        }
    }

    public class BapaImpl : BapaFormula
    {
        private readonly BapaFormula _assumption;
        private readonly BapaFormula _conclusion;

        public BapaImpl(BapaFormula assumption, BapaFormula conclusion)
        {
            _assumption = assumption;
            _conclusion = conclusion;
        }

        public override string ToOcamlBapa()
        {
            return $"Impl({_assumption.ToOcamlBapa()}, {_conclusion.ToOcamlBapa()})";
        }
    }

    public class BapaNatRelation : BapaFormula
    {
        private readonly NatRelation _operation;
        private readonly BapaNatExpression _expr1;
        private readonly BapaNatExpression _expr2;

        public enum NatRelation
        {
            Less,
            Leq,
            Greater,
            Geq,
            Inteq,
            Intneq
        }

        public BapaNatRelation(NatRelation operation, BapaNatExpression expr1, BapaNatExpression expr2)
        {
            _operation = operation;
            _expr1 = expr1;
            _expr2 = expr2;
        }

        public override string ToOcamlBapa()
        {
            return $"{_operation} ({_expr1.ToOcamlBapa()}, {_expr2.ToOcamlBapa()})";
        }
    }

    public class BapaSetRelation : BapaFormula
    {
        private readonly SetRelation _operation;
        private readonly BapaSetExpression _expr1;
        private readonly BapaSetExpression _expr2;

        public enum SetRelation
        {
            Subset,
            Subseteq
        }

        public BapaSetRelation(SetRelation operation, BapaSetExpression expr1, BapaSetExpression expr2)
        {
            _operation = operation;
            _expr1 = expr1;
            _expr2 = expr2;
        }

        public override string ToOcamlBapa()
        {
            return $"{_operation} ({_expr1.ToOcamlBapa()}, {_expr2.ToOcamlBapa()})";
        }
    }

    public class BapaFormulaOperation : BapaFormula
    {
        private readonly NatRelation _operation;
        private readonly BapaFormula[] _formulas;

        public enum NatRelation
        {
            And,
        }

        public BapaFormulaOperation(NatRelation operation, BapaFormula[] formulas)
        {
            _operation = operation;
            _formulas = formulas;
        }

        public override string ToOcamlBapa()
        {
            return $"{_operation} [{string.Join("; ", _formulas.Select(expr => expr.ToOcamlBapa()).ToArray())}]";
        }
    }

    public class BapaNotFormula : BapaFormula
    {
        private readonly BapaFormula _inner;

        public BapaNotFormula(BapaFormula inner)
        {
            _inner = inner;
        }

        public override string ToOcamlBapa()
        {
            return $"Not ({_inner.ToOcamlBapa()})";
        }
    }
}
