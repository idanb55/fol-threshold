using System;
using System.Runtime.Serialization;

namespace FolThresholdParser
{
    [Serializable]
    internal class MultipleDefinitionsOfIdentifier : Exception
    {
        private Token token;

        public MultipleDefinitionsOfIdentifier()
        {
        }

        public MultipleDefinitionsOfIdentifier(string message) : base(message)
        {
        }

        public MultipleDefinitionsOfIdentifier(Token token)
        {
            this.token = token;
        }

        public MultipleDefinitionsOfIdentifier(string message, Exception innerException) : base(message, innerException)
        {
        }

        protected MultipleDefinitionsOfIdentifier(SerializationInfo info, StreamingContext context) : base(info, context)
        {
        }
    }
}