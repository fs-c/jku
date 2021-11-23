#include <stdio.h> 
#include <stdlib.h>

struct list 
{ 
    int data; 
    struct list *next; 
}; 

struct list *start, *end; 

void add(struct list **head, struct list **tail, int theData) 
{ 
    if (*tail==NULL) { 
        *head = *tail = (struct list *)malloc(sizeof(struct list)); 
        (*head)->data = theData; 
        (*head)->next = NULL; 
    } else { 
        (*tail)->next = (struct list *)malloc(sizeof(struct list)); 
        *tail = (*tail)->next; 
        (*tail)->data = theData; 
        (*tail)->next = NULL; 
    } 
} 

void delete (struct list **head, struct list **tail) 
{ 
    struct list *temp; 
    if (*head==*tail) { 
        free(*head); 
        *head = *tail = NULL; 
    } else { 
        temp = (*head)->next; 
        free(*head); 
        (*head) = temp; 
    } 
} 

int main(void) 
{ 
   start=end=NULL; 
   printf("Adding '2'\n"); 
   add(&start, &end, 2); 
   printf("Adding '3'\n"); 
   add(&start, &end, 3); 
   printf("First element: %d\n", start->data); 
   printf("Deleting one\n"); 
   delete(&start, &end); 
   printf("New first element: %d\n", start->data); 
   /* Memory leak - two malloc but only one free! */
   return 0;
} 
