using System;
using System.Collections.Generic;
using System.Linq;

namespace FolThresholdParser
{
    public abstract class SetExpression : IExpression
    {
        public abstract IEnumerable<string> Variables { get; }
    }

    public class SetVarExpression : SetExpression
    {
        protected string name;

        public SetVarExpression(string name) : base()
        {
            this.name = name;
        }

        public override IEnumerable<string> Variables
        {
            get
            {
                yield return name;
            }
        }
    }

    public class SetOpExpression : SetExpression
    {
        protected SetExpression expr1;
        protected SyntaxKind op;
        protected SetExpression expr2;

        public override IEnumerable<string> Variables
        {
            get
            {
                return expr1.Variables.Concat(expr2.Variables);
            }
        }

        public SetOpExpression(SetExpression expr1, SyntaxKind setOperation, SetExpression expr2)
        {
            this.expr1 = expr1;
            this.op = setOperation;
            this.expr2 = expr2;
        }
    }

    public class SetComplementExpression : SetExpression
    {
        protected SetExpression expr;

        public SetComplementExpression(SetExpression expr)
        {
            this.expr = expr;
        }

        public override IEnumerable<string> Variables
        {
            get
            {
                return expr.Variables;
            }
        }
    }
}
