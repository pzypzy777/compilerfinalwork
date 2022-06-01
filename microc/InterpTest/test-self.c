void main(int n) {
   int i;
   int a;
   i=0;
   do {
      print("%d", ++i);
   }  
   while(i<n);
   println;
   i=0;
   do {
       print("%d",i++);
   }  
   while(i<n);
   println;
   i=20;
   do {
      print("%d",i--);
   } 
   while(i>n); 
   println;
   i=20;
   do {
      print("%d",--i);
   }  
   while(i>n);
}

