namespace FolThresholdParser
{
    public class Identifier
    {
        public bool Constant { get; protected set; }
        public string Name { get; protected set; }

        public Identifier(bool constant, string name)
        {
            Name = name;
            Constant = constant;
        }
    }

    public class Natural : Identifier
    {
        public Natural(bool constant, string name) : base(constant, name) { }
    }

    public class Quorum : Identifier
    {
        public SyntaxKind Operation { get; protected set; }
        public NaturalExpression Expression { get; protected set; }

        public Quorum(bool constant, string name, SyntaxKind operation, NaturalExpression expression) : base(constant, name)
        {
            Operation = operation;
            Expression = expression;
        }
    }
}
