
void rewind_scope() ;
void enter_scope( named_node *parent ) ;
void exit_scope () ;
void push_scope( named_node *parent, named_node *child ) ;
void pop_scope() ;
void addname_to_scope( named_node *scope, named_node *new );
void addname( named_node *new ) ;
named_node *findname_in_scope( named_node *scope, char *name ) ;
named_node *findname( char *name ) ;

named_node *new_node(
  char *name, 
  SV_name_type  type, 
  int add_to_scope 
) ;
